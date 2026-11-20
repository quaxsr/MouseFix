// MouseRemapper —— 全局鼠标按键映射工具（.NET 8 WinExe，NativeAOT，纯 Win32 API，无任何 UI 框架）
//
// 旧版三大致命问题的修复方式：
//  1) 退出热键无效            → RegisterHotKey 绑定到消息窗口句柄，WM_HOTKEY 在 WndProc 中处理；
//  2) 卡死后系统鼠标左键假死  → 所有退出路径（退出热键 / 托盘"彻底退出" / WM_CLOSE / WM_DESTROY /
//     未捕获异常）统一走 Cleanup()：若当前处于"to 键已注入按下未抬起"状态，先按绝对坐标强制补发
//     一个抬起事件，再卸钩子、注销热键、删除托盘图标，系统绝不会停留在"按住左键"状态；
//  3) 点不动浏览器右上角等系统 UI → app.manifest 声明 requireAdministrator（绕过 UIPI 拦截），
//     且注入一律使用 MOUSEEVENTF_ABSOLUTE 归一化绝对坐标（严禁 dx=dy=0 相对注入）。
using System;
using System.IO;
using System.Runtime.InteropServices;
using System.Text.Json;
using System.Text.Json.Serialization;

internal static class Program
{
    // ================= Win32 常量 =================
    private const int  WH_MOUSE_LL      = 14;
    private const uint LLMHF_INJECTED   = 0x0001;

    private const uint WM_NULL    = 0x0000;
    private const uint WM_DESTROY = 0x0002;
    private const uint WM_CLOSE   = 0x0010;
    private const uint WM_COMMAND = 0x0111;
    private const uint WM_HOTKEY  = 0x0312;
    private const uint WM_APP_TRAY = 0x8001;            // WM_APP + 1：托盘回调消息

    private const uint WM_LBUTTONDOWN = 0x0201, WM_LBUTTONUP  = 0x0202;
    private const uint WM_RBUTTONDOWN = 0x0204, WM_RBUTTONUP  = 0x0205;
    private const uint WM_MBUTTONDOWN = 0x0207, WM_MBUTTONUP  = 0x0208;
    private const uint WM_XBUTTONDOWN = 0x020B, WM_XBUTTONUP  = 0x020C;
    private const uint WM_LBUTTONDBLCLK = 0x0203;

    private const uint MOUSEEVENTF_MOVE       = 0x0001;
    private const uint MOUSEEVENTF_LEFTDOWN   = 0x0002;
    private const uint MOUSEEVENTF_LEFTUP     = 0x0004;
    private const uint MOUSEEVENTF_RIGHTDOWN  = 0x0008;
    private const uint MOUSEEVENTF_RIGHTUP    = 0x0010;
    private const uint MOUSEEVENTF_MIDDLEDOWN = 0x0020;
    private const uint MOUSEEVENTF_MIDDLEUP   = 0x0040;
    private const uint MOUSEEVENTF_XDOWN      = 0x0080;
    private const uint MOUSEEVENTF_XUP        = 0x0100;
    private const uint MOUSEEVENTF_ABSOLUTE   = 0x8000;
    private const uint MOUSEEVENTF_VIRTUALDESK = 0x4000;

    private const uint MOD_ALT     = 0x0001;
    private const uint MOD_CONTROL = 0x0002;
    private const uint MOD_SHIFT   = 0x0004;
    private const uint MOD_WIN     = 0x0008;

    private const uint NIM_ADD = 0, NIM_MODIFY = 1, NIM_DELETE = 2;
    private const uint NIF_MESSAGE = 0x1, NIF_ICON = 0x2, NIF_TIP = 0x4;

    private const uint MF_STRING       = 0x0000;
    private const uint MF_SEPARATOR    = 0x0800;
    private const uint TPM_RIGHTBUTTON = 0x0002;
    private const uint INPUT_MOUSE     = 0;
    private const int  SM_CXSCREEN     = 0;
    private const int  SM_CYSCREEN     = 1;
    private const int  SM_XVIRTUALSCREEN  = 76;
    private const int  SM_YVIRTUALSCREEN  = 77;
    private const int  SM_CXVIRTUALSCREEN = 78;
    private const int  SM_CYVIRTUALSCREEN = 79;
    private const int  IDI_APPLICATION = 32512;
    private static readonly IntPtr HWND_MESSAGE = new(-3); // 消息专用窗口

    private const uint   HOTKEY_ID = 1;
    private const uint   TRAY_ID   = 1;
    private const int    IDM_TOGGLE = 1;                   // 托盘菜单命令号：开启/暂停映射
    private const int    IDM_EXIT   = 2;                   // 托盘菜单命令号：彻底退出
    private const string CLASS_NAME = "MouseRemapperTrayWnd";
    private const uint   MB_ICONERROR = 0x10, MB_TOPMOST = 0x40000;

    // ================= 运行状态 =================
    private static readonly LowLevelMouseProc s_hookProc = HookProc; // 静态字段保活，防 GC 回收钩子回调
    private static readonly WndProcDelegate   s_wndProc = WndProc;  // 静态字段保活窗口过程

    private static MouseBtn s_from = MouseBtn.Middle;  // 拦截键（config.json "from"）
    private static MouseBtn s_to   = MouseBtn.Left;    // 注入键（config.json "to"）
    private static uint     s_hotkeyMods = MOD_ALT | MOD_CONTROL;
    private static uint     s_hotkeyVk   = 0x51;       // 'Q'
    private static string   s_hotkeyText = "Ctrl+Alt+Q";

    private static IntPtr s_hHook = IntPtr.Zero;
    private static IntPtr s_hWnd  = IntPtr.Zero;
    private static bool   s_enabled     = true;  // 映射开关（托盘可切换）
    private static bool   s_injectedDown = false; // to 键已注入按下且尚未抬起
    private static bool   s_cleanedUp    = false; // Cleanup 幂等标志
    private static bool   s_trayAdded    = false;

    private static int Main()
    {
        // 任何未捕获异常同样走 Cleanup：补发悬空抬起 → 卸钩子 → 注销热键 → 删除托盘图标
        AppDomain.CurrentDomain.UnhandledException += OnUnhandledException;
        try
        {
            Run();
        }
        catch
        {
            Cleanup();
            return 1;
        }
        return 0;
    }

    private static void OnUnhandledException(object? sender, UnhandledExceptionEventArgs e)
    {
        Cleanup();
    }

    private static void Run()
    {
        LoadConfig();

        IntPtr hInstance = GetModuleHandleW(null);

        // 隐藏原生消息窗口：接收托盘回调消息与 WM_HOTKEY
        var wc = new WNDCLASSW
        {
            lpfnWndProc = s_wndProc,
            hInstance = hInstance,
            lpszClassName = CLASS_NAME,
        };
        if (RegisterClassW(ref wc) == 0)
            Fatal("注册托盘窗口类失败（Win32 错误码 " + Marshal.GetLastWin32Error() + "）。");

        s_hWnd = CreateWindowExW(0, CLASS_NAME, "MouseRemapper", 0, 0, 0, 0, 0,
                                 HWND_MESSAGE, IntPtr.Zero, hInstance, IntPtr.Zero);
        if (s_hWnd == IntPtr.Zero)
            Fatal("创建托盘消息窗口失败（Win32 错误码 " + Marshal.GetLastWin32Error() + "）。");

        // 退出热键：组合键来自 config.json，绑定到消息窗口（WM_HOTKEY 在 WndProc 处理）
        if (!RegisterHotKey(s_hWnd, HOTKEY_ID, s_hotkeyMods, s_hotkeyVk))
            Fatal("注册退出热键失败（" + s_hotkeyText + "，可能已被其他程序或实例占用）。");

        s_hHook = SetWindowsHookExW(WH_MOUSE_LL, s_hookProc, hInstance, 0);
        if (s_hHook == IntPtr.Zero)
            Fatal("安装 WH_MOUSE_LL 低级鼠标钩子失败（Win32 错误码 " + Marshal.GetLastWin32Error() + "）。");

        AddTrayIcon();

        // 单线程消息泵：托盘回调、WM_HOTKEY、WM_COMMAND 全部经 GetMessageW 分发到 WndProc。
        // 返回 0 = 收到 WM_QUIT，-1 = 出错，两者都结束循环并兜底清理。
        while (true)
        {
            int ret = GetMessageW(out MSG msg, IntPtr.Zero, 0, 0);
            if (ret <= 0)
                break;
            TranslateMessage(ref msg);
            DispatchMessageW(ref msg);
        }

        Cleanup(); // 消息泵结束后的兜底清理（Cleanup 幂等）
    }

    // ================= 配置加载（config.json，位于 exe 同目录） =================
    private const string DefaultConfigJson =
        "{\n  \"from\": \"Middle\",\n  \"to\": \"Left\",\n  \"exit_hotkey\": \"Ctrl+Alt+Q\"\n}\n";

    private static void LoadConfig()
    {
        string fromStr   = "Middle";
        string toStr     = "Left";
        string hotkeyStr = "Ctrl+Alt+Q";

        try
        {
            string path = Path.Combine(AppContext.BaseDirectory, "config.json");
            if (!File.Exists(path))
                File.WriteAllText(path, DefaultConfigJson); // 不存在：自动生成默认配置再读取
            string json = File.ReadAllText(path);
            AppConfig? cfg = JsonSerializer.Deserialize(json, AppJsonContext.Default.AppConfig);
            if (cfg != null)
            {
                if (!string.IsNullOrWhiteSpace(cfg.From))        fromStr   = cfg.From.Trim();
                if (!string.IsNullOrWhiteSpace(cfg.To))          toStr     = cfg.To.Trim();
                if (!string.IsNullOrWhiteSpace(cfg.ExitHotkey))  hotkeyStr = cfg.ExitHotkey.Trim();
            }
        }
        catch
        {
            // 读取/解析失败：保持内置默认值继续运行，绝不因配置问题崩溃
        }

        s_from = MouseBtn.Parse(fromStr) ?? MouseBtn.Middle;
        s_to   = MouseBtn.Parse(toStr) ?? MouseBtn.Left;

        if (TryParseHotkey(hotkeyStr, out uint mods, out uint vk))
        {
            s_hotkeyMods = mods;
            s_hotkeyVk = vk;
            s_hotkeyText = hotkeyStr;
        }
        else
        {
            s_hotkeyMods = MOD_ALT | MOD_CONTROL; // 解析失败回退默认 Ctrl+Alt+Q
            s_hotkeyVk = 0x51;
            s_hotkeyText = "Ctrl+Alt+Q";
        }
    }

    private static bool TryParseHotkey(string text, out uint mods, out uint vk)
    {
        mods = 0;
        vk = 0;
        if (string.IsNullOrWhiteSpace(text))
            return false;
        foreach (string raw in text.Split('+'))
        {
            string part = raw.Trim();
            if (part.Length == 0)
                return false;
            switch (part.ToLowerInvariant())
            {
                case "ctrl": case "control": mods |= MOD_CONTROL; continue;
                case "alt":                  mods |= MOD_ALT;     continue;
                case "shift":                mods |= MOD_SHIFT;   continue;
                case "win": case "windows":  mods |= MOD_WIN;     continue;
            }
            if (vk != 0)
                return false; // 不允许出现两个主键
            if (!TryParseVk(part, out vk))
                return false;
        }
        return vk != 0;
    }

    private static bool TryParseVk(string token, out uint vk)
    {
        vk = 0;
        string s = token.ToUpperInvariant();
        if (s.Length == 1)
        {
            char c = s[0];
            if ((c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'))
            {
                vk = c; // 单个字母/数字的 ASCII 即 VK 码（'Q' = 0x51）
                return true;
            }
            return false;
        }
        if (s.Length >= 2 && s[0] == 'F' && uint.TryParse(s.AsSpan(1), out uint f) && f >= 1 && f <= 24)
        {
            vk = 0x70u + f - 1u; // F1..F24
            return true;
        }
        vk = s switch
        {
            "ESC" or "ESCAPE"          => 0x1B,
            "TAB"                      => 0x09,
            "SPACE"                    => 0x20,
            "ENTER" or "RETURN"        => 0x0D,
            "BACKSPACE" or "BACK"      => 0x08,
            "DELETE" or "DEL"          => 0x2E,
            "INSERT" or "INS"          => 0x2D,
            "HOME"                     => 0x24,
            "END"                      => 0x23,
            "PAGEUP" or "PGUP"         => 0x21,
            "PAGEDOWN" or "PGDN"       => 0x22,
            "LEFT"                     => 0x25,
            "UP"                       => 0x26,
            "RIGHT"                    => 0x27,
            "DOWN"                     => 0x28,
            "PAUSE"                    => 0x13,
            "SCROLLLOCK" or "SCROLL"   => 0x91,
            _ => 0,
        };
        return vk != 0;
    }

    // ================= WH_MOUSE_LL 钩子回调（与消息泵同线程） =================
    private static IntPtr HookProc(int nCode, IntPtr wParam, IntPtr lParam)
    {
        if (nCode < 0)
            return CallNextHookEx(s_hHook, nCode, wParam, lParam);

        MSLLHOOKSTRUCT info;
        unsafe { info = *(MSLLHOOKSTRUCT*)lParam; } // 热路径指针解引用，零封送开销

        // 注入事件一律放行：SendInput 产生的事件会再次进入本钩子，放行以防注入递归
        if ((info.flags & LLMHF_INJECTED) != 0)
            return CallNextHookEx(s_hHook, nCode, wParam, lParam);

        // 暂停状态：所有事件原样放行，不注入
        if (!s_enabled)
            return CallNextHookEx(s_hHook, nCode, wParam, lParam);

        // 只拦截配置的 from 键，其余事件全部放行
        if (!s_from.Matches((uint)wParam, info.mouseData))
            return CallNextHookEx(s_hHook, nCode, wParam, lParam);

        bool down = s_from.IsDownEvent((uint)wParam, info.mouseData);
        InjectButton(s_to, down, info.pt); // 用钩子事件里的 pt.X/pt.Y 做绝对坐标注入
        s_injectedDown = down;

        return (IntPtr)1; // 吞掉 from 键事件，不 CallNextHookEx
    }

    // ================= 绝对坐标注入（严禁 dx=dy=0 相对注入） =================
    private static void InjectButton(MouseBtn btn, bool down, POINT pt)
    {
        // WH_MOUSE_LL 回调的 pt 是虚拟屏幕坐标（多显示器时可为负或超出主屏范围），
        // 故按虚拟屏幕原点/尺寸归一化并搭配 MOUSEEVENTF_VIRTUALDESK；
        // 单显示器时虚拟屏幕与主屏重合，结果与按主屏 SM_CXSCREEN/SM_CYSCREEN 归一化一致
        int vx = GetSystemMetrics(SM_XVIRTUALSCREEN);
        int vy = GetSystemMetrics(SM_YVIRTUALSCREEN);
        int vw = GetSystemMetrics(SM_CXVIRTUALSCREEN);
        int vh = GetSystemMetrics(SM_CYVIRTUALSCREEN);
        if (vw < 1) vw = 1920; // 防御性兜底，正常不会发生
        if (vh < 1) vh = 1080;

        // 虚拟屏幕坐标 → 0..65535 归一化绝对坐标
        int nx = (int)Math.Clamp(((long)pt.X - vx) * 65536 / vw, 0L, 65535L);
        int ny = (int)Math.Clamp(((long)pt.Y - vy) * 65536 / vh, 0L, 65535L);

        var input = new INPUT
        {
            type = INPUT_MOUSE,
            mi = new MOUSEINPUT
            {
                dx = nx,
                dy = ny,
                mouseData = btn.XIndex, // 仅 X1/X2 需要（XBUTTON1=1 / XBUTTON2=2），其余为 0
                dwFlags = MOUSEEVENTF_ABSOLUTE | MOUSEEVENTF_VIRTUALDESK | MOUSEEVENTF_MOVE | (down ? btn.DownFlag : btn.UpFlag),
                time = 0,
                dwExtraInfo = IntPtr.Zero,
            },
        };
        _ = SendInput(1, ref input, Marshal.SizeOf<INPUT>()); // cbSize = 整个 INPUT 大小（x64 = 40）
    }

    // ================= 统一退出清理（所有退出路径共用，幂等） =================
    private static void Cleanup()
    {
        if (s_cleanedUp)
            return;
        s_cleanedUp = true;

        // 1) 若 to 键仍处于"注入按下未抬起"状态，先按绝对坐标强制补发抬起，
        //    否则系统永远停留在"按住左键"状态，鼠标左键假死
        if (s_injectedDown)
        {
            s_injectedDown = false;
            GetCursorPos(out POINT p);
            InjectButton(s_to, false, p);
        }

        // 2) 卸载低级鼠标钩子
        if (s_hHook != IntPtr.Zero)
        {
            UnhookWindowsHookEx(s_hHook);
            s_hHook = IntPtr.Zero;
        }

        // 3) 注销退出热键
        UnregisterHotKey(s_hWnd != IntPtr.Zero ? s_hWnd : IntPtr.Zero, HOTKEY_ID);

        // 4) 删除托盘图标
        if (s_trayAdded)
        {
            var nid = new NOTIFYICONDATAW
            {
                cbSize = (uint)Marshal.SizeOf<NOTIFYICONDATAW>(),
                hWnd = s_hWnd,
                uID = TRAY_ID,
            };
            _ = Shell_NotifyIconW(NIM_DELETE, ref nid);
            s_trayAdded = false;
        }
    }

    // ================= 窗口过程：托盘回调 / 热键 / 菜单命令 =================
    private static IntPtr WndProc(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam)
    {
        switch (msg)
        {
            case WM_APP_TRAY: // 托盘回调消息（lParam 低 16 位为鼠标消息）
            {
                uint trayMsg = (uint)((long)lParam & 0xFFFF);
                if (trayMsg == WM_LBUTTONDBLCLK)
                    ToggleMapping();  // 双击托盘图标：切换映射状态
                else if (trayMsg == WM_RBUTTONUP)
                    ShowTrayMenu();   // 右键托盘图标：弹出菜单
                return IntPtr.Zero;
            }
            case WM_COMMAND: // TrackPopupMenu 选中的菜单命令
            {
                int id = (int)((long)wParam & 0xFFFF); // LOWORD(wParam) = 菜单命令号
                if (id == IDM_TOGGLE)
                    ToggleMapping();
                else if (id == IDM_EXIT)
                {
                    Cleanup();           // 先补发悬空抬起 → 卸钩子 → 注销热键 → 删除托盘图标
                    DestroyWindow(hWnd); // 触发 WM_DESTROY → PostQuitMessage
                }
                return IntPtr.Zero;
            }
            case WM_HOTKEY: // 退出热键（组合键来自 config.json）
                Cleanup();
                PostQuitMessage(0);
                return IntPtr.Zero;
            case WM_CLOSE:
                Cleanup();
                DestroyWindow(hWnd);
                return IntPtr.Zero;
            case WM_DESTROY:
                Cleanup(); // 幂等，重复调用安全
                PostQuitMessage(0);
                return IntPtr.Zero;
            default:
                return DefWindowProcW(hWnd, msg, wParam, lParam);
        }
    }

    // ================= 托盘 =================
    private static void AddTrayIcon()
    {
        IntPtr hIcon = IntPtr.Zero;
        string? exe = Environment.ProcessPath;
        if (!string.IsNullOrEmpty(exe))
        {
            IntPtr[] large = new IntPtr[1];
            IntPtr[] small = new IntPtr[1];
            if (ExtractIconExW(exe, 0, large, small, 1) != 0)
                hIcon = small[0] != IntPtr.Zero ? small[0] : large[0];
        }
        if (hIcon == IntPtr.Zero)
            hIcon = LoadIconW(IntPtr.Zero, (IntPtr)IDI_APPLICATION); // 提取失败回退默认应用图标

        var nid = new NOTIFYICONDATAW
        {
            cbSize = (uint)Marshal.SizeOf<NOTIFYICONDATAW>(),
            hWnd = s_hWnd,
            uID = TRAY_ID,
            uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP,
            uCallbackMessage = WM_APP_TRAY,
            hIcon = hIcon,
            szTip = s_enabled ? "MouseRemapper 映射中" : "MouseRemapper 已暂停",
        };
        s_trayAdded = Shell_NotifyIconW(NIM_ADD, ref nid);
    }

    private static void UpdateTrayTip()
    {
        if (!s_trayAdded || s_hWnd == IntPtr.Zero)
            return;
        var nid = new NOTIFYICONDATAW
        {
            cbSize = (uint)Marshal.SizeOf<NOTIFYICONDATAW>(),
            hWnd = s_hWnd,
            uID = TRAY_ID,
            uFlags = NIF_TIP,
            szTip = s_enabled ? "MouseRemapper 映射中" : "MouseRemapper 已暂停",
        };
        _ = Shell_NotifyIconW(NIM_MODIFY, ref nid);
    }

    private static void ShowTrayMenu()
    {
        if (s_hWnd == IntPtr.Zero)
            return;

        IntPtr menu = CreatePopupMenu();
        if (menu == IntPtr.Zero)
            return;

        // 菜单项文字按当前状态动态显示
        _ = AppendMenuW(menu, MF_STRING, (UIntPtr)IDM_TOGGLE, s_enabled ? "暂停映射" : "开启映射");
        _ = AppendMenuW(menu, MF_SEPARATOR, UIntPtr.Zero, null);
        _ = AppendMenuW(menu, MF_STRING, (UIntPtr)IDM_EXIT, "彻底退出");

        GetCursorPos(out POINT p);
        SetForegroundWindow(s_hWnd); // 经典托盘菜单焦点技巧，否则点击菜单外区域菜单不消失
        _ = TrackPopupMenu(menu, TPM_RIGHTBUTTON, p.X, p.Y, 0, s_hWnd, IntPtr.Zero);
        _ = PostMessageW(s_hWnd, WM_NULL, IntPtr.Zero, IntPtr.Zero);
        _ = DestroyMenu(menu);
    }

    private static void ToggleMapping()
    {
        s_enabled = !s_enabled;

        // 暂停瞬间若 to 键仍处于注入按下状态，立即补发抬起，避免悬空
        if (!s_enabled && s_injectedDown)
        {
            s_injectedDown = false;
            GetCursorPos(out POINT p);
            InjectButton(s_to, false, p);
        }
        UpdateTrayTip();
    }

    // ================= 致命错误：清理后弹窗退出 =================
    private static void Fatal(string message)
    {
        Cleanup();
        _ = MessageBoxW(IntPtr.Zero, message, "MouseRemapper", MB_ICONERROR | MB_TOPMOST);
        Environment.Exit(1);
    }

    // ================= 鼠标按键定义 =================
    private sealed class MouseBtn
    {
        public readonly string Name;
        public readonly uint DownMsg;    // WH_MOUSE_LL 的 wParam（非 X 键）
        public readonly uint UpMsg;
        public readonly uint DownFlag;   // SendInput 的 MOUSEEVENTF_*
        public readonly uint UpFlag;
        public readonly ushort XIndex;   // X1/X2 为 1/2，其余为 0

        private MouseBtn(string name, uint downMsg, uint upMsg, uint downFlag, uint upFlag, ushort xIndex)
        {
            Name = name;
            DownMsg = downMsg;
            UpMsg = upMsg;
            DownFlag = downFlag;
            UpFlag = upFlag;
            XIndex = xIndex;
        }

        public static readonly MouseBtn Left   = new("Left",   WM_LBUTTONDOWN, WM_LBUTTONUP, MOUSEEVENTF_LEFTDOWN,   MOUSEEVENTF_LEFTUP,   0);
        public static readonly MouseBtn Right  = new("Right",  WM_RBUTTONDOWN, WM_RBUTTONUP, MOUSEEVENTF_RIGHTDOWN,  MOUSEEVENTF_RIGHTUP,  0);
        public static readonly MouseBtn Middle = new("Middle", WM_MBUTTONDOWN, WM_MBUTTONUP, MOUSEEVENTF_MIDDLEDOWN, MOUSEEVENTF_MIDDLEUP, 0);
        public static readonly MouseBtn X1     = new("X1",     WM_XBUTTONDOWN, WM_XBUTTONUP, MOUSEEVENTF_XDOWN,      MOUSEEVENTF_XUP,      1);
        public static readonly MouseBtn X2     = new("X2",     WM_XBUTTONDOWN, WM_XBUTTONUP, MOUSEEVENTF_XDOWN,      MOUSEEVENTF_XUP,      2);

        public static MouseBtn? Parse(string text)
        {
            return text.ToLowerInvariant() switch
            {
                "left"   => Left,
                "right"  => Right,
                "middle" => Middle,
                "x1"     => X1,
                "x2"     => X2,
                _ => null,
            };
        }

        // 该事件是否属于本按键（X 键编号在钩子事件 mouseData 高 16 位）
        public bool Matches(uint msg, uint mouseData)
        {
            if (XIndex == 0)
                return msg == DownMsg || msg == UpMsg;
            if (msg != WM_XBUTTONDOWN && msg != WM_XBUTTONUP)
                return false;
            return (ushort)(mouseData >> 16) == XIndex;
        }

        public bool IsDownEvent(uint msg, uint mouseData)
        {
            return XIndex == 0
                ? msg == DownMsg
                : msg == WM_XBUTTONDOWN && (ushort)(mouseData >> 16) == XIndex;
        }
    }

    // ================= Win32 结构体 =================
    [StructLayout(LayoutKind.Sequential)]
    private struct POINT
    {
        public int X;
        public int Y;
    }

    // WH_MOUSE_LL 回调 lParam 所指结构（x64：8+4+4+4+(4 对齐)+8 = 32 字节）
    [StructLayout(LayoutKind.Sequential)]
    private struct MSLLHOOKSTRUCT
    {
        public POINT pt;
        public uint mouseData;     // X 按钮编号在高 16 位
        public uint flags;         // LLMHF_INJECTED 等标志
        public uint time;
        public IntPtr dwExtraInfo;
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct MOUSEINPUT
    {
        public int dx;
        public int dy;
        public uint mouseData;
        public uint dwFlags;
        public uint time;
        public IntPtr dwExtraInfo; // x64 下 8 字节，使结构按 8 对齐（32 字节）
    }

    // INPUT 联合体：x64 下 type 占 4 字节 + 4 对齐，联合体起点偏移 8，总长 40 字节
    [StructLayout(LayoutKind.Explicit)]
    private struct INPUT
    {
        [FieldOffset(0)] public uint type;
        [FieldOffset(8)] public MOUSEINPUT mi;
    }

    // MSG（x64 原生 sizeof(MSG)=48；lPrivate 原生为 DWORD，声明为 uint 保持与 winuser.h 一致的 48 字节布局）
    [StructLayout(LayoutKind.Sequential)]
    private struct MSG
    {
        public IntPtr hwnd;
        public uint message;
        public IntPtr wParam;
        public IntPtr lParam;
        public uint time;
        public POINT pt;
        public uint lPrivate;
    }

    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    private struct WNDCLASSW
    {
        public uint style;
        public WndProcDelegate lpfnWndProc;
        public int cbClsExtra;
        public int cbWndExtra;
        public IntPtr hInstance;
        public IntPtr hIcon;
        public IntPtr hCursor;
        public IntPtr hbrBackground;
        public string? lpszMenuName;
        public string lpszClassName;
    }

    // NOTIFYICONDATAW 完整布局（V3 + hBalloonIcon），cbSize 由 Marshal.SizeOf 计算，勿手写
    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    private struct NOTIFYICONDATAW
    {
        public uint cbSize;
        public IntPtr hWnd;
        public uint uID;
        public uint uFlags;
        public uint uCallbackMessage;
        public IntPtr hIcon;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 128)] public string? szTip;
        public uint dwState;
        public uint dwStateMask;
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 256)] public string? szInfo;
        public uint uTimeout;   // DUMMYUNIONNAME：原生定义中 uTimeout 与 uVersion 是同一 UINT 的 union，只声明这一个字段（4 字节），保证 sizeof=976 与字段偏移和原生一致
        [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 64)] public string? szInfoTitle;
        public uint dwInfoFlags;
        public Guid guidItem;
        public IntPtr hBalloonIcon;
    }

    // ================= Win32 P/Invoke =================
    internal delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);
    internal delegate IntPtr WndProcDelegate(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern IntPtr SetWindowsHookExW(int idHook, LowLevelMouseProc lpfn, IntPtr hMod, uint dwThreadId);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool UnhookWindowsHookEx(IntPtr hhk);

    [DllImport("user32.dll")]
    private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern uint SendInput(uint cInputs, ref INPUT pInputs, int cbSize);

    [DllImport("user32.dll")]
    private static extern int GetSystemMetrics(int nIndex);

    [DllImport("user32.dll")]
    private static extern bool GetCursorPos(out POINT lpPoint);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool RegisterHotKey(IntPtr hWnd, uint id, uint fsModifiers, uint vk);

    [DllImport("user32.dll")]
    private static extern bool UnregisterHotKey(IntPtr hWnd, uint id);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern int GetMessageW(out MSG lpMsg, IntPtr hWnd, uint wMsgFilterMin, uint wMsgFilterMax);

    [DllImport("user32.dll")]
    private static extern bool TranslateMessage(ref MSG lpMsg);

    [DllImport("user32.dll")]
    private static extern IntPtr DispatchMessageW(ref MSG lpMsg);

    [DllImport("user32.dll")]
    private static extern void PostQuitMessage(int nExitCode);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern IntPtr LoadIconW(IntPtr hInstance, IntPtr lpIconName);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern IntPtr GetModuleHandleW(string? lpModuleName);

    [DllImport("user32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
    private static extern IntPtr CreateWindowExW(uint dwExStyle, string lpClassName, string lpWindowName,
        uint dwStyle, int x, int y, int nWidth, int nHeight, IntPtr hWndParent, IntPtr hMenu,
        IntPtr hInstance, IntPtr lpParam);

    [DllImport("user32.dll")]
    private static extern bool DestroyWindow(IntPtr hWnd);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern ushort RegisterClassW(ref WNDCLASSW lpWndClass);

    [DllImport("user32.dll")]
    private static extern IntPtr DefWindowProcW(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll")]
    private static extern bool PostMessageW(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll")]
    private static extern bool SetForegroundWindow(IntPtr hWnd);

    [DllImport("user32.dll")]
    private static extern IntPtr CreatePopupMenu();

    [DllImport("user32.dll")]
    private static extern bool DestroyMenu(IntPtr hMenu);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern bool AppendMenuW(IntPtr hMenu, uint uFlags, UIntPtr uIDNewItem, string? lpNewItem);

    [DllImport("user32.dll")]
    private static extern bool TrackPopupMenu(IntPtr hMenu, uint uFlags, int x, int y,
        int nReserved, IntPtr hWnd, IntPtr prcRect);

    [DllImport("shell32.dll")]
    private static extern bool Shell_NotifyIconW(uint dwMessage, ref NOTIFYICONDATAW lpData);

    [DllImport("shell32.dll", CharSet = CharSet.Unicode)]
    private static extern uint ExtractIconExW(string lpszFile, int nIconIndex,
        IntPtr[] phIconLarge, IntPtr[] phIconSmall, uint nIcons);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern int MessageBoxW(IntPtr hWnd, string text, string caption, uint uType);
}

// ================= 配置模型与 System.Text.Json 源生成（NativeAOT 必需，反射序列化在 AOT 下会失败） =================
public sealed class AppConfig
{
    [JsonPropertyName("from")]
    public string From { get; set; } = "Middle";

    [JsonPropertyName("to")]
    public string To { get; set; } = "Left";

    [JsonPropertyName("exit_hotkey")]
    public string ExitHotkey { get; set; } = "Ctrl+Alt+Q";
}

[JsonSourceGenerationOptions(WriteIndented = true)]
[JsonSerializable(typeof(AppConfig))]
internal sealed partial class AppJsonContext : JsonSerializerContext
{
}
