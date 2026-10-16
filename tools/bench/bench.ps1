# Times two builds of multi_k_searcher against each other on the runs in
# suites.txt and checks that both find exactly the same pairs.
#
#   powershell -ExecutionPolicy Bypass -File bench.ps1 -Old <folder or exe> -New <folder or exe> [-Threads 6] [-Repeats 3]
#
# -Threads defaults to all logical processors, -Repeats to 3 (the median time
# is reported).  The runs alternate old/new so both see the same machine
# conditions.  The report is printed and saved as bench_report.txt next to
# this script.  Works in Windows PowerShell 5.1 and PowerShell 7.
param(
    [Parameter(Mandatory = $true)][string]$Old,
    [Parameter(Mandatory = $true)][string]$New,
    [int]$Threads = 0,
    [int]$Repeats = 3,
    [string]$Suites = ""
)
$ErrorActionPreference = "Stop"
$here = $PSScriptRoot
if (-not $Suites) { $Suites = Join-Path $here "suites.txt" }
if ($Threads -le 0) { $Threads = [Environment]::ProcessorCount }

function Resolve-Program([string]$p) {
    if (Test-Path -LiteralPath $p -PathType Container) { $p = Join-Path $p "multi_k_searcher.exe" }
    if (-not (Test-Path -LiteralPath $p)) { throw "program not found: $p" }
    return (Resolve-Path -LiteralPath $p).Path
}
$oldExe = Resolve-Program $Old
$newExe = Resolve-Program $New

$work = Join-Path ([IO.Path]::GetTempPath()) ("amicable_bench_" + [Guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Force -Path $work | Out-Null
$report = Join-Path $here "bench_report.txt"

function Get-Pairs([string]$dir) {
    $files = @(Get-ChildItem -LiteralPath (Join-Path $dir "Data") -Recurse -Filter multi_k_results.txt -ErrorAction SilentlyContinue)
    $lines = @()
    foreach ($f in $files) { $lines += @(Get-Content -LiteralPath $f.FullName | Where-Object { $_ -match '^[0-9]+=' }) }
    return @($lines | Sort-Object -Unique)
}

function Invoke-Run([string]$exe, [string]$dir, [string]$hash, [string]$k0, [string]$k1) {
    if (Test-Path -LiteralPath $dir) { Remove-Item -LiteralPath $dir -Recurse -Force }
    New-Item -ItemType Directory -Force -Path $dir | Out-Null
    $out = Join-Path $dir "out.txt"
    $argList = @("--root", "`"$dir`"", "--mode", "range", "--hash", "`"$hash`"", "--workers", "$Threads",
                 "--timeout", "0", "--report", "0", $k0, $k1)
    # Process.WaitForExit, not Start-Process -Wait: in Windows PowerShell the
    # latter only notices the end about once a second, which rounded every
    # time up to the next whole second
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $exe
    $psi.Arguments = $argList -join " "
    $psi.UseShellExecute = $false
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.WorkingDirectory = $dir
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $p = [Diagnostics.Process]::Start($psi)
    $so = $p.StandardOutput.ReadToEndAsync()
    $se = $p.StandardError.ReadToEndAsync()
    $p.WaitForExit()
    $sw.Stop()
    [IO.File]::WriteAllText($out, $so.Result)
    [IO.File]::WriteAllText((Join-Path $dir "err.txt"), $se.Result)
    $text = $so.Result + $se.Result
    if ($p.ExitCode -ne 0 -or $text -notmatch "complete: every k") {
        foreach ($f in @($out, (Join-Path $dir "err.txt"))) {
            if (Test-Path -LiteralPath $f) { Get-Content -LiteralPath $f -Tail 15 | ForEach-Object { Say "  | $_" } }
        }
        throw "run failed or did not complete (exit code $($p.ExitCode)): $exe"
    }
    return $sw.Elapsed.TotalSeconds
}

function Get-Median([double[]]$v) {
    $s = @($v | Sort-Object)
    $n = $s.Count
    if ($n % 2 -eq 1) { return $s[($n - 1) / 2] }
    return ($s[$n / 2 - 1] + $s[$n / 2]) / 2
}

$lines = New-Object System.Collections.Generic.List[string]
function Say([string]$s) { Write-Host $s; $lines.Add($s) }

Say "old: $oldExe"
Say "new: $newExe"
Say ("threads: {0}   repeats: {1}   {2}" -f $Threads, $Repeats, (Get-Date))
Say ("{0,-34} {1,9} {2,9} {3,8}  {4}" -f "run", "old (s)", "new (s)", "speedup", "same pairs")
$totOld = 0.0; $totNew = 0.0; $allSame = $true
try {
    foreach ($line in Get-Content -LiteralPath $Suites) {
        if ($line -match '^\s*#' -or $line.Trim() -eq "") { continue }
        $f = $line.Split('|') | ForEach-Object { $_.Trim() }
        $name = $f[0]; $hash = $f[1]; $k0 = $f[2]; $k1 = $f[3]
        $to = @(); $tn = @(); $same = ""
        for ($r = 0; $r -lt $Repeats; $r++) {
            $to += Invoke-Run $oldExe (Join-Path $work "old") $hash $k0 $k1
            $po = Get-Pairs (Join-Path $work "old")
            $tn += Invoke-Run $newExe (Join-Path $work "new") $hash $k0 $k1
            $pn = Get-Pairs (Join-Path $work "new")
            if (($po -join "`n") -ne ($pn -join "`n")) {
                $allSame = $false
                $same = "NO (old $($po.Count), new $($pn.Count) lines)"
                break
            }
            $same = "yes ($([int]($pn.Count / 2)) pairs)"
        }
        $mo = Get-Median $to; $mn = Get-Median $tn
        $totOld += $mo; $totNew += $mn
        Say ("{0,-34} {1,9:N2} {2,9:N2} {3,7:N2}x  {4}" -f $name, $mo, $mn, ($mo / $mn), $same)
    }
    $verdict = if ($allSame) { "all runs found the same pairs" } else { "PAIRS DIFFER" }
    Say ("{0,-34} {1,9:N2} {2,9:N2} {3,7:N2}x  {4}" -f "total", $totOld, $totNew, ($totOld / $totNew), $verdict)
} catch {
    Say "ERROR: $($_.Exception.Message)"
    $allSame = $false
} finally {
    Set-Content -LiteralPath $report -Value $lines
    Remove-Item -LiteralPath $work -Recurse -Force -ErrorAction SilentlyContinue
}
Write-Host ""
Write-Host "Report saved to $report"
if (-not $allSame) { exit 1 }
exit 0
