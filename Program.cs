// ============================================================================
// ECARSWatcher
// Code Version: VER17
// Baseline: VER16 (last known good running version)
// Changes in VER17:
//   1) Title base text: "ECARS Watcher by NJ2US" + version in title bar
//   2) Remove visible blue row-selection highlight (selection still works)
//   3) Allow user to hide/show columns via View menu and header right-click,
//      with persistence to settings.json (Time column always visible) and
//      a Reset Columns option.
// ============================================================================

#nullable enable
﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.Globalization;
using System.IO;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Timers;
using System.Windows.Forms;
using System.Windows.Automation;
using System.Reflection;
using System.Text.Json;

using System.Linq;

internal static class Program
{
    // VER17: settings storage root
    private static readonly string AppDataRoot =
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "ECARSWatcher");


    // =========================
    // VERSIONING
    // =========================
    public const string CodeVersion = "VER17";
    public static readonly string AppVersion = GetAppVersion();

    private static string GetAppVersion()
    {
        var asm = Assembly.GetExecutingAssembly();
        var info = asm.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion;
        if (!string.IsNullOrWhiteSpace(info))
            return info.Split('+')[0]; // trim build metadata if present

        return asm.GetName().Version?.ToString() ?? "0.0.0";
    }


    // =========================
    // APP IDENTITY / PATHS
    // =========================
    private const string AppName = "ECARS Call Sign Watcher (AUTO LOOKUP)";
    private const string MutexName = @"Global\ECARSWatcher_SingleInstance_v1";

    // UI Automation targets (from Inspect.exe)
    private const string CallSignAutomationId = "TboCallSign";
    private const string EcarsNoAutomationId = "TboECARSNo";

    // Lookup endpoint (public)
    private const string LookupUrlTemplate = "https://www.ecars7255.com/membership/results.aspx?search={0}";

    // Debounce / call validation
    private const int MinLen = 4;
    private static readonly TimeSpan CacheTtl = TimeSpan.FromMinutes(15);
    private static readonly int MaxRows = 500;

    // Font persistence
    private const float BaseFontSize = 12.0f;
    private const float MinFontSize = 8.0f;
    private const float MaxFontSize = 22.0f;
    private const float FontStep = 1.0f;
    private static float CurrentFontSize = BaseFontSize;

    private static string CurrentFontName = "Segoe UI";
    private static FontStyle CurrentFontStyle = FontStyle.Regular;

    // Per-user data dir
    private static readonly string BaseDir =
        Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "ECARSWatcher");

    private static readonly string LogDir = Path.Combine(BaseDir, "logs");
    private static readonly string LogFile = Path.Combine(LogDir, "ecarswatcher.log");
    // Settings (persist user UI preferences)
    private static readonly string SettingsPath =
        Path.Combine(AppDataRoot, "settings.json");

    private sealed class UserSettings
    {
        public List<string>? VisibleColumns { get; set; }
    }

    private static UserSettings LoadUserSettings()
    {
        try
        {
            if (File.Exists(SettingsPath))
            {
                var json = File.ReadAllText(SettingsPath, Encoding.UTF8);
                var s = JsonSerializer.Deserialize<UserSettings>(json);
                return s ?? new UserSettings();
            }
        }
        catch { /* ignore corrupt settings */ }
        return new UserSettings();
    }

    private static void SaveUserSettings(UserSettings s)
    {
        try
        {
            Directory.CreateDirectory(AppDataRoot);
            var json = JsonSerializer.Serialize(s, new JsonSerializerOptions { WriteIndented = true });
            File.WriteAllText(SettingsPath, json, Encoding.UTF8);
        }
        catch { /* ignore */ }
    }


    private static readonly string CsvFile = Path.Combine(BaseDir, "ledger.csv");
    private static readonly string SettingsFile = Path.Combine(BaseDir, "settings.ini");

    // =========================
    // RUNTIME STATE
    // =========================
    private static CheckInForm? Form;

    // Application context (owns tray lifetime)
    // Keeps a WinForms timer alive so the tray icon can be re-registered with Explorer after the message loop starts.
    private static readonly object Gate = new object();
    private static string PendingValue = "";
    private static string LastLookedUp = "";

    private static readonly System.Timers.Timer DebounceTimer = new System.Timers.Timer();
    private static CancellationTokenSource LookupCts;

    private class CacheEntry { public MemberResult Result; public DateTime WhenUtc; }
    private static readonly Dictionary<string, CacheEntry> Cache = new Dictionary<string, CacheEntry>(StringComparer.OrdinalIgnoreCase);

    private static readonly HttpClient Http = BuildHttpClient();

    // single instance
    private static Mutex SingleInstanceMutex;

    // used to allow “real exit”
    private static bool AllowExit = false;

    [STAThread]
    public static void Main()
    {
        // -------------------------
        // SINGLE INSTANCE
        // -------------------------
        bool createdNew;
        SingleInstanceMutex = new Mutex(true, MutexName, out createdNew);
        if (!createdNew)
        {
            // already running — try to bring it forward
            TryBringExistingToFront();
            return;
        }

        // -------------------------
        // WINDOWS FORMS INIT
        // -------------------------
        Application.SetHighDpiMode(HighDpiMode.SystemAware);
        Application.EnableVisualStyles();
        Application.SetCompatibleTextRenderingDefault(false);

        Directory.CreateDirectory(LogDir);
        EnsureCsvHeader();
        LoadSettings();

        LogPreflightHeader();

        // Build the ledger window
        Form = new CheckInForm(
            openFolder: OpenLogsFolder,
            clearCache: ClearCache,
            clearLedger: ClearLedger,
            maxRows: MaxRows,
            increaseFont: IncreaseFont,
            decreaseFont: DecreaseFont,
            resetFont: ResetFont,
            requestExit: RequestExit
        );

        Form!.ApplyFontSize(CurrentFontSize);

        // tray icon
        // Tray removed in VER15 (ledger menu only)

        // UIA watcher
        StartWatcher();

        // show the ledger on startup (no hiding)

        // Run the main form as the message pump owner.
        // The tray icon stays alive as long as the app is running.
        Application.Run(Form!);
    }

    // =========================
    // TRAY / ICONS
    // =========================
        // (removed in VER15)


    private static Icon GetAppIconOrFallback()
    {
        // Prefer an explicit .ico file next to the EXE. This is the most reliable for NotifyIcon.
        // (We have seen ExtractAssociatedIcon occasionally return a blank/invalid handle depending on build layout.)
        try
        {
            string iconPath = Path.Combine(AppContext.BaseDirectory, "ecarslogo.ico");
            if (File.Exists(iconPath))
            {
                Log("Tray icon source: " + iconPath);
                return new Icon(iconPath);
            }
            Log("Tray icon file not found: " + iconPath + " (falling back)");
        }
        catch (Exception ex)
        {
            Log("Tray icon file load failed: " + ex);
        }

        // Fallback: EXE-associated icon.
        try
        {
            Icon? ico = Icon.ExtractAssociatedIcon(Application.ExecutablePath);
            if (ico != null) return ico;
        }
        catch (Exception ex)
        {
            Log("ExtractAssociatedIcon failed: " + ex);
        }

        return SystemIcons.Application;
    }
private static Font MakeUiFont(float size, FontStyle? styleOverride = null, string? nameOverride = null)
{
    string name = string.IsNullOrWhiteSpace(nameOverride) ? CurrentFontName : nameOverride!;
    FontStyle style = styleOverride ?? CurrentFontStyle;

    try
    {
        return new Font(name, size, style, GraphicsUnit.Point);
    }
    catch
    {
        return new Font("Segoe UI", size, style, GraphicsUnit.Point);
    }
}




    // =========================
    // APPLICATION CONTEXT (OWNS LIFETIME)
    // =========================



    private static void RequestExit()
    {
        // Signal "real exit" so FormClosing handlers can allow shutdown.
        AllowExit = true;
        try
        {
            if (Form != null && !Form.IsDisposed)
            {
                // Close the ledger window (this will unwind Application.Run(Form))
                Form.Close();
            }
        }
        catch { }

        try { Application.Exit(); } catch { }
    }


    // =========================
    // UIA WATCHER
    // =========================
    private static void StartWatcher()
    {
        DebounceTimer.Interval = 700;
        DebounceTimer.AutoReset = false;
        DebounceTimer.Elapsed += DebounceTimer_Elapsed;

        Automation.AddAutomationPropertyChangedEventHandler(
            AutomationElement.RootElement,
            TreeScope.Subtree,
            OnPropertyChanged,
            ValuePattern.ValueProperty);

        Log("Watcher started. Watching AutomationId=" + CallSignAutomationId);
    }

    private static void DebounceTimer_Elapsed(object sender, ElapsedEventArgs e)
    {
        Task.Run(async () => await DebounceFiredAsync());
    }

    private static void OnPropertyChanged(object sender, AutomationPropertyChangedEventArgs e)
    {
        try
        {
            AutomationElement element = sender as AutomationElement;
            if (element == null) return;

            if (!string.Equals(element.Current.AutomationId, CallSignAutomationId, StringComparison.Ordinal))
                return;

            object pat;
            if (!element.TryGetCurrentPattern(ValuePattern.Pattern, out pat))
                return;

            string value = ((ValuePattern)pat).Current.Value ?? "";

            lock (Gate)
            {
                PendingValue = value;
                DebounceTimer.Stop();
                DebounceTimer.Start();
            }
        }
        catch { }
    }

    private static async Task DebounceFiredAsync()
    {
        string raw;
        lock (Gate) raw = PendingValue ?? "";

        string call = NormalizeCallsign(raw);
        if (!IsPlausibleCall(call)) return;

        lock (Gate)
        {
            if (string.Equals(call, LastLookedUp, StringComparison.OrdinalIgnoreCase))
                return;
            LastLookedUp = call;
        }

        // Cache hit?
        CacheEntry ce;
        lock (Cache)
        {
            if (Cache.TryGetValue(call, out ce))
            {
                if ((DateTime.UtcNow - ce.WhenUtc) <= CacheTtl)
                {
                    ApplyResult(call, ce.Result, true);
                    return;
                }
                Cache.Remove(call);
            }
        }

        CancelInflightLookup();
        LookupCts = new CancellationTokenSource();
        CancellationToken token = LookupCts.Token;

        try
        {
            MemberResult result = await LookupEcarsAsync(call, token);
            if (token.IsCancellationRequested) return;

            lock (Cache)
            {
                Cache[call] = new CacheEntry { Result = result, WhenUtc = DateTime.UtcNow };
            }

            ApplyResult(call, result, false);
        }
        catch (TaskCanceledException)
        {
            // typing continued
        }
        catch (Exception ex)
        {
            Log("Lookup failed: " + ex);

            var entry = new CheckInEntry
            {
                Timestamp = DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"),
                CallSign = call,
                Status = "ERROR",
                Source = "live",
                Email = ex.Message ?? "Lookup error"
            };
            AddEntry(entry);
        }
    }

    // =========================
    // LOOKUP + PARSE
    // =========================
    private static async Task<MemberResult> LookupEcarsAsync(string call, CancellationToken token)
    {
        string url = string.Format(CultureInfo.InvariantCulture, LookupUrlTemplate, Uri.EscapeDataString(call));

        using (HttpResponseMessage resp = await Http.GetAsync(url, token))
        {
            if (!resp.IsSuccessStatusCode)
                throw new HttpRequestException("HTTP " + (int)resp.StatusCode + " " + resp.ReasonPhrase);

            string html = await resp.Content.ReadAsStringAsync();

            // Find first table; membership page is simple
            Match tableMatch = Regex.Match(html, @"<table\b[^>]*>(.*?)</table>", RegexOptions.IgnoreCase | RegexOptions.Singleline);
            if (!tableMatch.Success) return null;

            string tableHtml = tableMatch.Groups[1].Value;

            MatchCollection rowMatches = Regex.Matches(tableHtml, @"<tr\b[^>]*>(.*?)</tr>", RegexOptions.IgnoreCase | RegexOptions.Singleline);
            foreach (Match row in rowMatches)
            {
                // skip header rows that use <th>
                if (Regex.IsMatch(row.Value, @"<th\b", RegexOptions.IgnoreCase))
                    continue;

                MatchCollection td = Regex.Matches(row.Value, @"<td\b[^>]*>(.*?)</td>", RegexOptions.IgnoreCase | RegexOptions.Singleline);
                if (td.Count < 3) continue;

                string memberNum = HtmlToText(td[2].Groups[1].Value);
                if (!Regex.IsMatch(memberNum, @"^\d+$"))
                    continue;

                return new MemberResult
                {
                    CallSign = td.Count > 0 ? HtmlToText(td[0].Groups[1].Value) : call,
                    Name = td.Count > 1 ? HtmlToText(td[1].Groups[1].Value) : "",
                    MemberNumber = memberNum,
                    Expires = td.Count > 3 ? HtmlToText(td[3].Groups[1].Value) : "",
                    City = td.Count > 4 ? HtmlToText(td[4].Groups[1].Value) : "",
                    State = td.Count > 5 ? HtmlToText(td[5].Groups[1].Value) : "",
                    Email = td.Count > 6 ? HtmlToText(td[6].Groups[1].Value) : ""
                };
            }

            return null;
        }
    }

    private static string HtmlToText(string html)
    {
        if (string.IsNullOrEmpty(html)) return "";
        string noTags = Regex.Replace(html, "<.*?>", " ");
        string decoded = WebUtility.HtmlDecode(noTags);
        return Regex.Replace(decoded, @"\s+", " ").Trim();
    }

    private static HttpClient BuildHttpClient()
    {
        var handler = new HttpClientHandler
        {
            AllowAutoRedirect = true,
            AutomaticDecompression = DecompressionMethods.GZip | DecompressionMethods.Deflate
        };

        var client = new HttpClient(handler);
        client.Timeout = TimeSpan.FromSeconds(8);
        client.DefaultRequestHeaders.UserAgent.Clear();
        client.DefaultRequestHeaders.UserAgent.Add(new ProductInfoHeaderValue("ECARSWatcher", "1.0"));
        return client;
    }

    // =========================
    // APPLY RESULT / AUTOFILL
    // =========================
    private static void ApplyResult(string call, MemberResult result, bool fromCache)
    {
        var entry = new CheckInEntry
        {
            Timestamp = DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"),
            CallSign = call,
            Source = fromCache ? "cache" : "live"
        };

        if (result == null)
        {
            entry.Status = "NO MATCH";
            Log("No match: " + call + " (" + entry.Source + ")");
            AddEntry(entry);
            return;
        }

        AutofillEcarsNumber(result.MemberNumber);

        entry.Status = "MATCH";
        entry.Name = result.Name;
        entry.EcarsNo = result.MemberNumber;
        entry.Expires = result.Expires;
        entry.City = result.City;
        entry.State = result.State;
        entry.Email = result.Email;

        Log("Match: " + call + " -> " + result.MemberNumber + " (" + entry.Source + ")");
        AddEntry(entry);
    }

    private static void AutofillEcarsNumber(string ecarsNo)
    {
        if (!Regex.IsMatch(ecarsNo ?? "", @"^\d+$"))
            return;

        try
        {
            AutomationElement box =
                AutomationElement.RootElement.FindFirst(
                    TreeScope.Descendants,
                    new PropertyCondition(AutomationElement.AutomationIdProperty, EcarsNoAutomationId));

            if (box == null) return;

            object pat;
            if (!box.TryGetCurrentPattern(ValuePattern.Pattern, out pat))
                return;

            ((ValuePattern)pat).SetValue(ecarsNo);
        }
        catch { }
    }

    // =========================
    // LEDGER + CSV
    // =========================
    private static void AddEntry(CheckInEntry e)
    {
        AppendCsv(e);

        try
        {
            if (Form != null && !Form.IsDisposed)
                Form.BeginInvoke((Action)(() => Form.AddEntry(e)));
        }
        catch { }
    }

    private static void EnsureCsvHeader()
    {
        try
        {
            Directory.CreateDirectory(BaseDir);
            if (!File.Exists(CsvFile))
            {
                File.WriteAllText(CsvFile,
                    "Timestamp,CallSign,Name,ECARSNo,Expires,City,State,Email,Status,Source" + Environment.NewLine);
            }
        }
        catch { }
    }

    private static void AppendCsv(CheckInEntry e)
    {
        try
        {
            string Esc(string s)
            {
                if (s == null) s = "";
                s = s.Replace("\"", "\"\"");
                return "\"" + s + "\"";
            }

            string line =
                Esc(e.Timestamp) + "," +
                Esc(e.CallSign) + "," +
                Esc(e.Name) + "," +
                Esc(e.EcarsNo) + "," +
                Esc(e.Expires) + "," +
                Esc(e.City) + "," +
                Esc(e.State) + "," +
                Esc(e.Email) + "," +
                Esc(e.Status) + "," +
                Esc(e.Source) + Environment.NewLine;

            File.AppendAllText(CsvFile, line);
        }
        catch { }
    }

    // =========================
    // CACHE / UI ACTIONS
    // =========================
    private static void ClearCache()
    {
        lock (Cache) Cache.Clear();
        Log("Cache cleared by user.");
    }

    private static void ClearLedger()
    {
        if (Form != null && !Form.IsDisposed)
            Form.ClearRows();
        Log("Ledger cleared by user.");
    }

    // =========================
    // FONT ACTIONS
    // =========================
    private static void IncreaseFont() => SetFontSize(CurrentFontSize + FontStep);
    private static void DecreaseFont() => SetFontSize(CurrentFontSize - FontStep);
    private static void ResetFont() => SetFontSize(BaseFontSize);

    private static void SetFontSize(float newSize)
    {
        if (newSize < MinFontSize) newSize = MinFontSize;
        if (newSize > MaxFontSize) newSize = MaxFontSize;

        CurrentFontSize = newSize;
        SaveSettings();

        try { Form?.ApplyFontSize(CurrentFontSize); } catch { }
        Log("Font size set to " + CurrentFontSize.ToString("0.0", CultureInfo.InvariantCulture));
    }

    // =========================
    // SETTINGS
    // =========================
    private static void LoadSettings()
    {
        try
        {
            var p = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "settings.ini");
            if (!File.Exists(p)) return;

            foreach (var line in File.ReadAllLines(p))
            {
                var trimmed = line.Trim();
                if (string.IsNullOrWhiteSpace(trimmed)) continue;
                if (trimmed.StartsWith("#")) continue;
                var ix = trimmed.IndexOf('=');
                if (ix <= 0) continue;

                var key = trimmed.Substring(0, ix).Trim();
                var val = trimmed.Substring(ix + 1).Trim();

                if (key.Equals("FontSize", StringComparison.OrdinalIgnoreCase))
                {
                    float fs;
                    if (float.TryParse(val, NumberStyles.Float, CultureInfo.InvariantCulture, out fs))
                    {
                        CurrentFontSize = fs;
                    }
                }
                else if (key.Equals("FontName", StringComparison.OrdinalIgnoreCase))
                {
                    if (!string.IsNullOrWhiteSpace(val)) CurrentFontName = val;
                }
                else if (key.Equals("FontStyle", StringComparison.OrdinalIgnoreCase))
                {
                    int s;
                    if (int.TryParse(val, NumberStyles.Integer, CultureInfo.InvariantCulture, out s))
                    {
                        try { CurrentFontStyle = (FontStyle)s; } catch { /* ignore */ }
                    }
                }
            }
        }
        catch { /* ignore */ }
    }


    private static void SaveSettings()
    {
        try
        {
            var p = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "settings.ini");
            File.WriteAllText(p,
                "FontSize=" + CurrentFontSize.ToString("0.0", CultureInfo.InvariantCulture) + Environment.NewLine +
                "FontName=" + CurrentFontName + Environment.NewLine +
                "FontStyle=" + ((int)CurrentFontStyle).ToString(CultureInfo.InvariantCulture) + Environment.NewLine);
        }
        catch { /* ignore */ }
    }


    // =========================
    // NORMALIZE / VALIDATE
    // =========================
    private static string NormalizeCallsign(string raw)
    {
        if (raw == null) return "";
        string s = raw.Trim().ToUpperInvariant().Replace(" ", "");
        int slash = s.IndexOf('/');
        if (slash >= 0) s = s.Substring(0, slash);   // strips /P /M /QRP etc
        return s;
    }

    private static bool IsPlausibleCall(string call)
    {
        if (call.Length < MinLen) return false;
        if (call.Length > 12) return false;
        return Regex.IsMatch(call, "^[A-Z0-9]+$");
    }

    // =========================
    // CLEANUP / SUPPORT
    // =========================
    private static void CancelInflightLookup()
    {
        try
        {
            if (LookupCts != null)
            {
                LookupCts.Cancel();
                LookupCts.Dispose();
            }
        }
        catch { }
        finally { LookupCts = null; }
    }

    private static void OpenLogsFolder()
    {
        try
        {
            var psi = new ProcessStartInfo(LogDir) { UseShellExecute = true };
            Process.Start(psi);
        }
        catch { }
    }

    private static void Log(string msg)
    {
        try
        {
            File.AppendAllText(LogFile,
                DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss") + " " + msg + Environment.NewLine);
        }
        catch { }
    }

    private static void LogPreflightHeader()
    {
        try
        {
            Log("========================================");
            Log("Starting ECARSWatcher (ledger window). Font=" + CurrentFontSize.ToString("0.0", CultureInfo.InvariantCulture));
            Log("OS: " + System.Runtime.InteropServices.RuntimeInformation.OSDescription);
            Log("Process: " + (Environment.Is64BitProcess ? "x64" : "x86") + " | OS: " + (Environment.Is64BitOperatingSystem ? "x64" : "x86"));
            Log("Framework: " + System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription);
            Log("Install Dir: " + AppContext.BaseDirectory);
            Log("Log File: " + LogFile);
            Log("========================================");
        }
        catch { }
    }

    private static void ShowDiagnostics()
    {
        try
        {
            string summary = DiagnosticsKit.BuildSummary(AppName, GetVersionString(), "Tray/Ledger", LogFile, "https://www.ecars7255.com/");
            using (var dlg = new DiagnosticsForm("ECARSWatcher Diagnostics", summary, OpenLogsFolder))
                dlg.ShowDialog(Form);
        }
        catch (Exception ex)
        {
            Log("Diagnostics failed: " + ex);
            MessageBox.Show("Diagnostics failed: " + ex.Message, "ECARSWatcher", MessageBoxButtons.OK, MessageBoxIcon.Error);
        }
    }

    private static string GetVersionString()
    {
        try
        {
            var v = typeof(Program).Assembly.GetName().Version;
            return v == null ? "unknown" : v.ToString();
        }
        catch { return "unknown"; }
    }

    private static void TryBringExistingToFront()
    {
        // Best effort: find by window title and activate
        IntPtr hWnd = Native.FindWindow(null, CheckInForm.FullWindowTitle);
        if (hWnd != IntPtr.Zero)
        {
            Native.ShowWindow(hWnd, Native.SW_RESTORE);
            Native.SetForegroundWindow(hWnd);
        }
        else
        {
            // If ledger was hidden, user can still access tray manually
            // but at least avoid duplicate instance.
        }
    }

    // =========================
    // MODELS
    // =========================
    private sealed class MemberResult
    {
        public string CallSign;
        public string Name;
        public string MemberNumber;
        public string Expires;
        public string City;
        public string State;
        public string Email;
    }

    private sealed class CheckInEntry
    {
        public string Timestamp;
        public string CallSign;
        public string Name;
        public string EcarsNo;
        public string Expires;
        public string City;
        public string State;
        public string Email;
        public string Status; // MATCH / NO MATCH / ERROR
        public string Source; // live / cache
    }

    // =========================
    // LEDGER FORM
    // =========================
    private sealed class CheckInForm : Form
    {
        public const string WindowTitle = "ECARS Watcher by NJ2US";
        public static string FullWindowTitle => $"{WindowTitle} v{Program.AppVersion}";

        private readonly DataGridView Grid;
        private readonly Label Status;

        private readonly ToolStripMenuItem _viewColumnsMenu;
        private readonly ContextMenuStrip _headerColumnsMenu;
        private readonly Dictionary<string, ToolStripMenuItem> _viewColumnItems = new();
        private readonly Dictionary<string, ToolStripMenuItem> _headerColumnItems = new();
        private UserSettings _userSettings = new UserSettings();

        private bool _allowClose = false;

        private readonly Action _openFolder;
        private readonly Action _clearCache;
        private readonly Action _clearLedger;
        private readonly Action _fontUp;
        private readonly Action _fontDown;
        private readonly Action _fontReset;
        private readonly Action _exit;
        readonly FontDialog _fontDialog = new FontDialog();

        private readonly int _maxRows;

        public CheckInForm(
            Action openFolder,
            Action clearCache,
            Action clearLedger,
            int maxRows,
            Action increaseFont,
            Action decreaseFont,
            Action resetFont,
            Action requestExit
        )
        {
            _openFolder = openFolder;
            _clearCache = clearCache;
            _clearLedger = clearLedger;
            _maxRows = maxRows;
            _fontUp = increaseFont;
            _fontDown = decreaseFont;
            _fontReset = resetFont;
            _exit = requestExit;

            Text = FullWindowTitle;
            Width = 1200;
            Height = 580;
            StartPosition = FormStartPosition.CenterScreen;

            // match app icon for window
            try { Icon = GetAppIconOrFallback(); } catch { }

            // Menu
            var menu = new MenuStrip();

            var file = new ToolStripMenuItem("File");
            var miExit = new ToolStripMenuItem("Exit");
            miExit.ShortcutKeys = Keys.Alt | Keys.F4;
            miExit.Click += (s, e) => _exit();
            file.DropDownItems.Add(miExit);

            var view = new ToolStripMenuItem("View");
            var font = new ToolStripMenuItem("Font Size");

            var miUp = new ToolStripMenuItem("Increase");
            miUp.ShortcutKeys = Keys.Control | Keys.Oemplus;
            miUp.Click += (s, e) => _fontUp();

            var miDown = new ToolStripMenuItem("Decrease");
            miDown.ShortcutKeys = Keys.Control | Keys.OemMinus;
            miDown.Click += (s, e) => _fontDown();

            var miReset = new ToolStripMenuItem("Reset");
            miReset.ShortcutKeys = Keys.Control | Keys.D0;
            miReset.Click += (s, e) => _fontReset();

            font.DropDownItems.Add(miUp);
            font.DropDownItems.Add(miDown);
            font.DropDownItems.Add(new ToolStripSeparator());
            font.DropDownItems.Add(miReset);
            view.DropDownItems.Add(font);
            view.DropDownItems.Add(new ToolStripSeparator());
            var miFont = new ToolStripMenuItem("Font...", null, (s,e)=> ChooseFont());
            miFont.ShortcutKeys = Keys.Control | Keys.Shift | Keys.F;
            view.DropDownItems.Add(miFont);

            view.DropDownItems.Add(new ToolStripSeparator());
            _viewColumnsMenu = new ToolStripMenuItem("Columns");
            view.DropDownItems.Add(_viewColumnsMenu);

            _headerColumnsMenu = new ContextMenuStrip();


            var tools = new ToolStripMenuItem("Tools");

// Make top-level menu text bigger + bold (requested)
var topFont = new Font(menu.Font.FontFamily, menu.Font.SizeInPoints + 2f, FontStyle.Bold);
file.Font = topFont;
view.Font = topFont;
tools.Font = topFont;


            var miOpen = new ToolStripMenuItem("Open Logs Folder");
            miOpen.Click += (s, e) => _openFolder();
            var miClearCache = new ToolStripMenuItem("Clear Cache");
            miClearCache.Click += (s, e) => _clearCache();
            var miClearWin = new ToolStripMenuItem("Clear Window");
            miClearWin.Click += (s, e) => _clearLedger();

            tools.DropDownItems.Add(miOpen);
            tools.DropDownItems.Add(miClearCache);
            tools.DropDownItems.Add(miClearWin);

            menu.Items.Add(file);
            menu.Items.Add(view);
            menu.Items.Add(tools);

            MainMenuStrip = menu;
            Controls.Add(menu);

            // ---- Status line (top) + Grid (fill) ----
Status = new Label
{
    Dock = DockStyle.Top,
    Height = 28,
    Text = "Watching Call Sign box...",
    Padding = new Padding(10, 6, 10, 0),
    AutoEllipsis = true
};

Grid = new DataGridView
{
    Dock = DockStyle.Fill,
    ReadOnly = true,
    AllowUserToAddRows = false,
    AllowUserToDeleteRows = false,
    AllowUserToResizeRows = false,
    RowHeadersVisible = false,
    SelectionMode = DataGridViewSelectionMode.FullRowSelect,
    MultiSelect = false,
    AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.Fill,
    AutoSizeRowsMode = DataGridViewAutoSizeRowsMode.DisplayedCellsExceptHeaders,
    ColumnHeadersVisible = true,
    ColumnHeadersHeightSizeMode = DataGridViewColumnHeadersHeightSizeMode.AutoSize,
    BackgroundColor = SystemColors.Window,
    BorderStyle = BorderStyle.Fixed3D,
    CellBorderStyle = DataGridViewCellBorderStyle.Single,
    ColumnHeadersBorderStyle = DataGridViewHeaderBorderStyle.Single,
    RowHeadersBorderStyle = DataGridViewHeaderBorderStyle.None,
    EnableHeadersVisualStyles = false
};

// Make the grid readable (no "mystery meat" layout)
Grid.DefaultCellStyle.WrapMode = DataGridViewTriState.False;
Grid.DefaultCellStyle.Alignment = DataGridViewContentAlignment.MiddleLeft;
Grid.ColumnHeadersDefaultCellStyle.Alignment = DataGridViewContentAlignment.MiddleLeft;

// Selection: keep it functional but visually neutral (no Windows-blue highlight)
Grid.DefaultCellStyle.SelectionBackColor = Grid.DefaultCellStyle.BackColor;
Grid.DefaultCellStyle.SelectionForeColor = Grid.DefaultCellStyle.ForeColor;
Grid.ColumnHeadersDefaultCellStyle.SelectionBackColor = Grid.ColumnHeadersDefaultCellStyle.BackColor;
Grid.ColumnHeadersDefaultCellStyle.SelectionForeColor = Grid.ColumnHeadersDefaultCellStyle.ForeColor;


// Columns (explicit headers)
Grid.Columns.Add("Timestamp", "Time");
Grid.Columns.Add("CallSign", "Call");
Grid.Columns.Add("Name", "Name");
Grid.Columns.Add("ECARSNo", "ECARS#");
Grid.Columns.Add("Expires", "Expires");
Grid.Columns.Add("City", "City");
Grid.Columns.Add("State", "ST");
Grid.Columns.Add("Email", "Email");
Grid.Columns.Add("Status", "Status");
Grid.Columns.Add("Source", "Src");

// Reasonable starting widths
TrySetFillWeight("Timestamp", 12);
TrySetFillWeight("CallSign", 9);
TrySetFillWeight("Name", 18);
TrySetFillWeight("ECARSNo", 9);
TrySetFillWeight("Expires", 10);
TrySetFillWeight("City", 12);
TrySetFillWeight("State", 5);
TrySetFillWeight("Email", 18);
TrySetFillWeight("Status", 10);
TrySetFillWeight("Source", 5);


// Load persisted column visibility (settings.json)
_userSettings = Program.LoadUserSettings();

// Default: if no settings, show all columns
var visible = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
if (_userSettings.VisibleColumns != null)
{
    foreach (var c in _userSettings.VisibleColumns)
        if (!string.IsNullOrWhiteSpace(c))
            visible.Add(c.Trim());
}
// Enforce Time column always visible
visible.Add("Timestamp");

// Apply visibility to grid
foreach (DataGridViewColumn c in Grid.Columns)
{
    c.Visible = visible.Contains(c.Name);
}

// Build View->Columns menu and header right-click menu
void RefreshSettingsFromGridAndSave()
{
    var list = new List<string>();
    foreach (DataGridViewColumn c in Grid.Columns)
        if (c.Visible)
            list.Add(c.Name);

    // Enforce again, just in case
    if (!list.Any(x => string.Equals(x, "Timestamp", StringComparison.OrdinalIgnoreCase)))
        list.Insert(0, "Timestamp");

    _userSettings.VisibleColumns = list;
    Program.SaveUserSettings(_userSettings);
}

void SetColumnVisible(string colName, bool makeVisible, bool save = true)
{
    if (string.Equals(colName, "Timestamp", StringComparison.OrdinalIgnoreCase) && !makeVisible)
    {
        System.Media.SystemSounds.Beep.Play();
        return; // Time column stays
    }

    var col = Grid.Columns[colName];
    if (col == null) return;

    col.Visible = makeVisible;

    // Prevent hiding everything
    int visibleCount = 0;
    foreach (DataGridViewColumn c in Grid.Columns)
        if (c.Visible) visibleCount++;

    if (visibleCount == 0)
    {
        col.Visible = true;
        System.Media.SystemSounds.Beep.Play();
        return;
    }

    // Sync menu checkmarks
    if (_viewColumnItems.TryGetValue(colName, out var vItem)) vItem.Checked = makeVisible;
    if (_headerColumnItems.TryGetValue(colName, out var hItem)) hItem.Checked = makeVisible;

    if (save) RefreshSettingsFromGridAndSave();
}

void ResetColumnsToDefault()
{
    foreach (DataGridViewColumn c in Grid.Columns)
        c.Visible = true;

    // Always visible
    Grid.Columns["Timestamp"].Visible = true;

    foreach (var kv in _viewColumnItems) kv.Value.Checked = Grid.Columns[kv.Key].Visible;
    foreach (var kv in _headerColumnItems) kv.Value.Checked = Grid.Columns[kv.Key].Visible;

    RefreshSettingsFromGridAndSave();
}

void BuildColumnMenus()
{
    _viewColumnsMenu.DropDownItems.Clear();
    _headerColumnsMenu.Items.Clear();
    _viewColumnItems.Clear();
    _headerColumnItems.Clear();

    foreach (DataGridViewColumn c in Grid.Columns)
    {
        var headerText = c.HeaderText ?? c.Name;

        // View menu item
        var v = new ToolStripMenuItem(headerText)
        {
            CheckOnClick = true,
            Checked = c.Visible,
            Tag = c.Name
        };
        v.Click += (s, e) =>
        {
            var name = (string)((ToolStripMenuItem)s!).Tag!;
            SetColumnVisible(name, ((ToolStripMenuItem)s!).Checked);
        };
        _viewColumnsMenu.DropDownItems.Add(v);
        _viewColumnItems[c.Name] = v;

        // Header context menu item
        var h = new ToolStripMenuItem(headerText)
        {
            CheckOnClick = true,
            Checked = c.Visible,
            Tag = c.Name
        };
        h.Click += (s, e) =>
        {
            var name = (string)((ToolStripMenuItem)s!).Tag!;
            SetColumnVisible(name, ((ToolStripMenuItem)s!).Checked);
        };
        _headerColumnsMenu.Items.Add(h);
        _headerColumnItems[c.Name] = h;
    }

    // Separator + reset
    _viewColumnsMenu.DropDownItems.Add(new ToolStripSeparator());
    var resetView = new ToolStripMenuItem("Reset Columns");
    resetView.Click += (s, e) => ResetColumnsToDefault();
    _viewColumnsMenu.DropDownItems.Add(resetView);

    _headerColumnsMenu.Items.Add(new ToolStripSeparator());
    var resetHdr = new ToolStripMenuItem("Reset Columns");
    resetHdr.Click += (s, e) => ResetColumnsToDefault();
    _headerColumnsMenu.Items.Add(resetHdr);
}

BuildColumnMenus();

// Right-click on column header opens the same checklist
Grid.ColumnHeaderMouseClick += (s, e) =>
{
    if (e.Button == MouseButtons.Right)
    {
        var screen = Grid.PointToScreen(new Point(e.X, e.Y));
        _headerColumnsMenu.Show(screen);
    }
};

// Startup should look calm
Grid.ClearSelection();

var body = new Panel { Dock = DockStyle.Fill };
body.Controls.Add(Grid);
body.Controls.Add(Status);
Controls.Add(body);

            // Closing the ledger should EXIT (Captain said so).
FormClosing += (s, e) =>
{
    if (_allowClose)
        return;

    e.Cancel = true;
    _allowClose = true;
    _exit();
};
        }

        public void AllowCloseNow() => _allowClose = true;


private void TrySetFillWeight(string name, float weight)
{
    try
    {
        if (Grid.Columns.Contains(name))
            Grid.Columns[name].FillWeight = weight;
    }
    catch { }
}

public void ApplyFontSize(float size)
{
    // Use the user-selected font family + style from Program
    using Font f = Program.MakeUiFont(size);

    // Apply broadly
    this.Font = f;
    Grid.Font = f;
    Grid.DefaultCellStyle.Font = f;
    Grid.ColumnHeadersDefaultCellStyle.Font = f;
    Status.Font = f;

    foreach (DataGridViewColumn col in Grid.Columns)
        col.HeaderCell.Style.Font = f;

    try
    {
        Grid.AutoResizeColumns();
        Grid.AutoResizeRows();
    }
    catch { }
}

        void ChooseFont()
        {
            _fontDialog.ShowColor = false;
            _fontDialog.ShowEffects = true;
            _fontDialog.Font = Program.MakeUiFont(Program.CurrentFontSize);

            if (_fontDialog.ShowDialog(this) == DialogResult.OK)
            {
                Program.CurrentFontName = _fontDialog.Font.Name;
                Program.CurrentFontStyle = _fontDialog.Font.Style;
                Program.CurrentFontSize = _fontDialog.Font.Size;
                ApplyFontSize(Program.CurrentFontSize);
                Program.SaveSettings();
            }
        }


        public void AddEntry(CheckInEntry e)
        {
            Status.Text = e.Status + " - " + e.CallSign;

            int idx = Grid.Rows.Add(
                e.Timestamp, e.CallSign, e.Name, e.EcarsNo, e.Expires,
                e.City, e.State, e.Email, e.Status, e.Source);

            while (Grid.Rows.Count > _maxRows)
                Grid.Rows.RemoveAt(0);

            try { Grid.FirstDisplayedScrollingRowIndex = Grid.Rows.Count - 1; } catch { }

            try
            {
                var row = Grid.Rows[idx];
                if (e.Status == "MATCH") row.DefaultCellStyle.BackColor = Color.FromArgb(220, 255, 220);
                else if (e.Status == "NO MATCH") row.DefaultCellStyle.BackColor = Color.FromArgb(255, 245, 205);
                else if (e.Status == "ERROR") row.DefaultCellStyle.BackColor = Color.FromArgb(255, 220, 220);
            }
            catch { }
        }

        public void ClearRows()
        {
            Grid.Rows.Clear();
            Status.Text = "Cleared.";
        }
    }

    // =========================
    // DIAGNOSTICS SUPPORT
    // =========================
    private static class DiagnosticsKit
    {
        public static string BuildSummary(string appName, string appVersion, string component, string logFilePath, string apiBaseUrl)
        {
            var sb = new StringBuilder(4096);

            sb.AppendLine("========================================");
            sb.AppendLine(appName + " – Diagnostics Summary");
            sb.AppendLine("========================================");
            sb.AppendLine("Timestamp:      " + DateTimeOffset.Now.ToString("yyyy-MM-dd HH:mm:ss zzz"));
            sb.AppendLine("Component:      " + component);
            sb.AppendLine("App Version:    " + appVersion);
            sb.AppendLine("Process:        " + (Environment.Is64BitProcess ? "64-bit" : "32-bit") +
                          " (OS: " + (Environment.Is64BitOperatingSystem ? "64-bit" : "32-bit") + ")");
            sb.AppendLine("Machine:        " + Environment.MachineName);
            sb.AppendLine("User:           " + Environment.UserDomainName + "\\" + Environment.UserName);
            sb.AppendLine("Install Dir:    " + AppContext.BaseDirectory);
            sb.AppendLine("Log File:       " + logFilePath);
            sb.AppendLine("API Base URL:   " + apiBaseUrl);
            sb.AppendLine("OS:             " + System.Runtime.InteropServices.RuntimeInformation.OSDescription);
            sb.AppendLine("Framework:      " + System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription);

            sb.AppendLine();
            sb.AppendLine("---- Log Tail (last 120 lines) ----");
            sb.AppendLine(ReadTail(logFilePath, 120));

            sb.AppendLine("========================================");
            return sb.ToString();
        }

        private static string ReadTail(string path, int lines)
        {
            try
            {
                if (!File.Exists(path)) return "(Log file not found)";
                string[] all = File.ReadAllLines(path);
                int start = Math.Max(0, all.Length - Math.Max(1, lines));
                return string.Join(Environment.NewLine, all, start, all.Length - start);
            }
            catch (Exception ex)
            {
                return "(Unable to read log tail: " + ex.GetType().Name + ": " + ex.Message + ")";
            }
        }
    }

    private sealed class DiagnosticsForm : Form
    {
        private readonly TextBox _box;

        public DiagnosticsForm(string title, string text, Action openLogsFolder)
        {
            Text = title;
            StartPosition = FormStartPosition.CenterParent;
            Width = 900;
            Height = 650;
            MinimizeBox = false;

            _box = new TextBox
            {
                Multiline = true,
                ReadOnly = true,
                ScrollBars = ScrollBars.Both,
                WordWrap = false,
                Dock = DockStyle.Fill,
                Font = new Font(FontFamily.GenericMonospace, 9.0f),
                Text = text
            };

            var btnOpen = new Button { Text = "Open Logs Folder", AutoSize = true };
            var btnClose = new Button { Text = "Close", AutoSize = true };

            btnOpen.Click += (s, e) => openLogsFolder();
            btnClose.Click += (s, e) => Close();

            var panel = new FlowLayoutPanel
            {
                Dock = DockStyle.Bottom,
                Height = 48,
                FlowDirection = FlowDirection.RightToLeft,
                Padding = new Padding(8),
                WrapContents = false
            };
            panel.Controls.Add(btnClose);
            panel.Controls.Add(btnOpen);

            Controls.Add(_box);
            Controls.Add(panel);
        }
    }

    // =========================
    // NATIVE HELPERS
    // =========================
    private static class Native
    {
        public const int SW_RESTORE = 9;

        [System.Runtime.InteropServices.DllImport("user32.dll", SetLastError = true)]
        public static extern IntPtr FindWindow(string lpClassName, string lpWindowName);

        [System.Runtime.InteropServices.DllImport("user32.dll")]
        public static extern bool SetForegroundWindow(IntPtr hWnd);

        [System.Runtime.InteropServices.DllImport("user32.dll")]
        public static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);
    }
}