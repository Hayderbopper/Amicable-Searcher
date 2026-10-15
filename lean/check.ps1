# Builds the Lean formalization and runs every trust check (Windows PowerShell 5+ / pwsh).
# Exit code 0 only if all pass.
#
#   powershell -ExecutionPolicy Bypass -File .\check.ps1              build + checks, logs in logs/
#   powershell -ExecutionPolicy Bypass -File .\check.ps1 -SelfTest    also proves the checks
#                                                                    reject a planted sorry/axiom
#   powershell -ExecutionPolicy Bypass -File .\check.ps1 -SkipCache   no `lake exe cache get`
#
# If elan is missing it is installed from the official script (github.com/leanprover/elan),
# without a default toolchain: the pinned one in lean-toolchain is used.  Needs git.
#
# Step 2 downloads each dependency as a shallow copy of exactly the commit pinned in
# lake-manifest.json (the full Mathlib history that `lake` would clone otherwise is large and
# often fails on Windows with "invalid index-pack output").  Without the Mathlib cache, step 4
# compiles the ~1200 Mathlib files this project imports: 30-90 minutes, with progress shown.
#
# Windows tips: put this folder on a short path WITHOUT spaces (for example C:\lean\amicable);
# Mathlib's file names are long, and the script turns on git's core.longpaths for the
# dependencies it downloads.
param([switch]$SelfTest, [switch]$SkipCache)
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot
New-Item -ItemType Directory -Force -Path logs | Out-Null
$log = 'logs/check.log'
Set-Content -Path $log -Value '' -Encoding utf8

function Step($m) { "== $m" | Tee-Object -FilePath $log -Append }
function Note($m) { "$m" | Tee-Object -FilePath $log -Append }
function Fail($m) { "CHECK FAILED: $m" | Tee-Object -FilePath $log -Append; exit 1 }
function Run($exe, $argList, $outFile) {
  # runs a native command, output to $outFile, returns its exit code
  $p = Start-Process -FilePath $exe -ArgumentList $argList -NoNewWindow -Wait -PassThru `
         -RedirectStandardOutput $outFile -RedirectStandardError "$outFile.err"
  Get-Content "$outFile.err" -ErrorAction SilentlyContinue | Add-Content $outFile
  Remove-Item "$outFile.err" -ErrorAction SilentlyContinue
  return $p.ExitCode
}
function RunLive($exe, $argList, $outFile) {
  # runs a native command, shows its output as it comes and saves it to $outFile
  $old = $ErrorActionPreference; $ErrorActionPreference = 'Continue'
  & $exe @argList 2>&1 | ForEach-Object { "$_" } | Tee-Object -FilePath $outFile | Out-Host
  $code = $LASTEXITCODE
  $ErrorActionPreference = $old
  return $code
}
function Invoke-GitCmd($argList) {
  $old = $ErrorActionPreference; $ErrorActionPreference = 'Continue'
  & git -c core.longpaths=true @argList 2>&1 | ForEach-Object { "  $_" } | Out-Host
  $code = $LASTEXITCODE
  $ErrorActionPreference = $old
  return $code
}

$PinnedLean = 'leanprover/lean4:v4.34.1'
$PinnedMathlib = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
$elanBin = Join-Path (Join-Path $HOME '.elan') 'bin'
if (Test-Path $elanBin) { $env:PATH = "$elanBin$([IO.Path]::PathSeparator)$env:PATH" }

Step '1. toolchain'
if (-not (Get-Command elan -ErrorAction SilentlyContinue)) {
  Note 'elan not found: installing it (official elan-init.ps1, no default toolchain)'
  $init = Join-Path ([IO.Path]::GetTempPath()) 'elan-init.ps1'
  Invoke-WebRequest -UseBasicParsing -Uri 'https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1' -OutFile $init
  & $init -NoPrompt $true -DefaultToolchain none
  Remove-Item $init -ErrorAction SilentlyContinue
  $env:PATH = "$elanBin$([IO.Path]::PathSeparator)$env:PATH"
  if (-not (Get-Command elan -ErrorAction SilentlyContinue)) { Fail 'elan installation failed' }
}
if (-not (Get-Command git -ErrorAction SilentlyContinue)) { Fail 'git not found: install Git for Windows (https://git-scm.com)' }
if ($PSScriptRoot -match ' ') {
  Note "warning: this folder's path contains a space ($PSScriptRoot); if the build fails, copy the folder to a path without spaces, e.g. C:\lean\amicable"
}
if ((Get-Content lean-toolchain -Raw).Trim() -ne $PinnedLean) { Fail "lean-toolchain is not $PinnedLean" }
if (-not (Select-String -Path lake-manifest.json -SimpleMatch "`"rev`": `"$PinnedMathlib`"" -Quiet)) {
  Fail "lake-manifest.json does not pin mathlib $PinnedMathlib"
}
# Native stderr (elan prints "info: downloading ..." on the first `lean` call, which downloads
# the pinned toolchain, a few hundred MB) must not become an error under -ErrorAction Stop,
# so go through Run, which redirects it to a file.
Note "(the first `lean` call downloads the pinned toolchain if it is missing; this can take a few minutes)"
foreach ($t in @('elan', 'lean', 'lake')) {
  $null = Run $t @('--version') 'logs/version.tmp'
  Get-Content 'logs/version.tmp' | Tee-Object -FilePath $log -Append
  Remove-Item 'logs/version.tmp' -ErrorAction SilentlyContinue
}

Step '2. dependencies (shallow fetch of the commits pinned in lake-manifest.json)'
$manifest = Get-Content lake-manifest.json -Raw | ConvertFrom-Json
foreach ($pkg in $manifest.packages) {
  $dir = Join-Path '.lake/packages' $pkg.name
  $old = $ErrorActionPreference; $ErrorActionPreference = 'Continue'
  $head = if (Test-Path (Join-Path $dir '.git')) { (& git -C $dir rev-parse HEAD 2>$null) } else { '' }
  $ErrorActionPreference = $old
  if ($head -eq $pkg.rev) { Note "$($pkg.name): present"; continue }
  Note "$($pkg.name): fetching $($pkg.rev)"
  if (-not (Test-Path (Join-Path $dir '.git'))) {
    if (Test-Path $dir) { Remove-Item -Recurse -Force $dir }
    New-Item -ItemType Directory -Force -Path $dir | Out-Null
    if ((Invoke-GitCmd @('init', '-q', $dir)) -ne 0) { Fail "git init $dir" }
    if ((Invoke-GitCmd @('-C', $dir, 'remote', 'add', 'origin', $pkg.url)) -ne 0) { Fail "git remote add $dir" }
  }
  $null = Invoke-GitCmd @('-C', $dir, 'config', 'core.longpaths', 'true')
  $ok = $false
  foreach ($t in 1..3) {
    if ((Invoke-GitCmd @('-C', $dir, 'fetch', '--depth', '1', 'origin', $pkg.rev)) -eq 0) { $ok = $true; break }
    Note "  retry $t"; Start-Sleep -Seconds 5
  }
  if (-not $ok) { Fail "could not download $($pkg.name) from $($pkg.url)" }
  if ((Invoke-GitCmd @('-C', $dir, 'checkout', '-q', '--force', 'FETCH_HEAD')) -ne 0) { Fail "checkout $($pkg.name) (if it mentions 'Filename too long', move this folder to a shorter path)" }
}

Step '3. Mathlib cache (optional: without it, lake compiles the imported Mathlib files)'
if ($SkipCache) { Note 'skipped (-SkipCache)' }
else {
  Note 'lake exe cache get (gives up after 15 minutes)'
  $p = Start-Process -FilePath 'lake' -ArgumentList @('exe','cache','get') -NoNewWindow -PassThru `
         -RedirectStandardOutput 'logs/cache.log' -RedirectStandardError 'logs/cache.err'
  if (-not $p.WaitForExit(900000)) { try { $p.Kill() } catch {}; Note 'cache timed out (see logs/cache.log); building from source' }
  elseif ($p.ExitCode -eq 0) { Note 'cache OK' }
  else { Note 'cache unavailable (see logs/cache.log); building from source' }
}

Step '4. build (progress below; from source this takes 30-90 minutes the first time)'
if ((RunLive 'lake' @('build') 'logs/build.log') -ne 0) { Fail 'lake build failed (logs/build.log)' }
(Get-Content logs/build.log -Tail 1) | Tee-Object -FilePath $log -Append
if (Select-String -Path logs/build.log -SimpleMatch "declaration uses 'sorry'" -Quiet) { Fail 'a declaration uses sorry' }
$nwarn = @(Select-String -Path logs/build.log -Pattern '^warning').Count
Note "build warnings in AmicableProof: $nwarn"

Step '5. forbidden words in the library sources'
$src = @('AmicableProof.lean') + @(Get-ChildItem -Recurse -Filter *.lean AmicableProof | ForEach-Object FullName)
$hits = Select-String -Path $src -Pattern '\b(sorry|admit|native_decide|unsafe|implemented_by|extern)\b' -CaseSensitive
if ($hits) { $hits | Tee-Object -FilePath $log -Append; Fail 'forbidden word in the library (listed above)' }
$ax = Select-String -Path $src -Pattern '^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*axiom\s' -CaseSensitive
if ($ax) { $ax | Tee-Object -FilePath $log -Append; Fail 'axiom declaration in the library (listed above)' }
Note 'none found'

Step '6. axioms of every theorem (kernel-level: #print axioms for each)'
if ((Run 'lake' @('env','lean','CheckAxioms.lean') 'logs/axioms.log') -ne 0) {
  Get-Content logs/axioms.log -Tail 20; Fail 'axiom check failed (logs/axioms.log)'
}
$ok = Select-String -Path logs/axioms.log -Pattern '^AXIOM CHECK OK'
if (-not $ok) { Fail 'axiom check did not report OK' }
$ok.Line | Tee-Object -FilePath $log -Append

Step '7. open goals elaborate (Open/, outside the library; statements only)'
foreach ($f in Get-ChildItem Open -Filter *.lean -ErrorAction SilentlyContinue) {
  if ((Run 'lake' @('env','lean',"Open/$($f.Name)") "logs/open_$($f.BaseName).log") -ne 0) { Fail "$($f.Name) does not elaborate" }
  Note "Open/$($f.Name) elaborates"
}

if ($SelfTest) {
  Step '8. self-test: the checks must reject a planted sorry and a planted axiom'
  $T = 'AmicableProof/ZzSelfTest.lean'
  Copy-Item AmicableProof.lean logs/AmicableProof.lean.bak -Force
  try {
    Set-Content -Path $T -Value 'theorem zz_planted : 1 = 2 := by sorry' -Encoding ascii
    if (Select-String -Path $T -Pattern '\bsorry\b' -Quiet) { Note 'grep catches planted sorry: yes' } else { Fail 'grep missed planted sorry' }
    Add-Content -Path AmicableProof.lean -Value 'import AmicableProof.ZzSelfTest' -Encoding ascii
    Run 'lake' @('build','AmicableProof') 'logs/selftest_build.log' | Out-Null
    if ((Run 'lake' @('env','lean','CheckAxioms.lean') 'logs/selftest_axioms.log') -eq 0) { Fail 'axiom check accepted a sorry' }
    if (Select-String -Path logs/selftest_axioms.log -SimpleMatch 'sorryAx' -Quiet) { Note 'axiom check rejects planted sorry (sorryAx): yes' }
    Set-Content -Path $T -Value "axiom zz_planted_ax : 1 = 2`ntheorem zz_uses : 1 = 2 := zz_planted_ax" -Encoding ascii
    if (Select-String -Path $T -Pattern '^\s*axiom\s' -Quiet) { Note 'grep catches planted axiom: yes' }
    Run 'lake' @('build','AmicableProof') 'logs/selftest_build2.log' | Out-Null
    if ((Run 'lake' @('env','lean','CheckAxioms.lean') 'logs/selftest_axioms2.log') -eq 0) { Fail 'axiom check accepted an axiom' }
    if (Select-String -Path logs/selftest_axioms2.log -SimpleMatch 'axiom declared' -Quiet) { Note 'axiom check rejects planted axiom: yes' }
  } finally {
    Copy-Item logs/AmicableProof.lean.bak AmicableProof.lean -Force
    Remove-Item $T, logs/AmicableProof.lean.bak -ErrorAction SilentlyContinue
  }
  if ((Run 'lake' @('build') 'logs/selftest_rebuild.log') -ne 0) { Fail 'rebuild after self-test failed' }
  Note 'self-test passed; library restored'
}

Note 'ALL CHECKS PASSED'
exit 0
