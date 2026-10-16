# Downloads Microsoft's mimalloc allocator (MIT licence, see
# mimalloc\src\LICENSE) at the release this project was tested with into
# third_party\mimalloc\src.  build.ps1 runs this by itself when it is missing
# and compiles its single-file build (src\static.c) into the programs.
# Needs git (Git for Windows, or MSYS2's git).
$ErrorActionPreference = "Stop"

$here = $PSScriptRoot
$dir = Join-Path $here "mimalloc\src"
$commit = "8c532c32c3c96e5ba1f2283e032f69ead8add00f"     # v2.1.7

$git = (Get-Command git -ErrorAction SilentlyContinue).Source
if (-not $git) {
    foreach ($c in @("C:\msys64\usr\bin\git.exe", "C:\Program Files\Git\cmd\git.exe")) {
        if (Test-Path -LiteralPath $c) { $git = $c; break }
    }
}
if (-not $git) { throw "git not found: install Git for Windows, or in MSYS2 run  pacman -S git" }

function Invoke-Git {
    & $git @args
    if ($LASTEXITCODE -ne 0) { throw "git $($args -join ' ') failed" }
}

Write-Host "fetching mimalloc..."
if (-not (Test-Path -LiteralPath (Join-Path $dir ".git"))) {
    if (Test-Path -LiteralPath $dir) { Remove-Item -LiteralPath $dir -Recurse -Force }
    Invoke-Git init -q $dir
    Invoke-Git -C $dir remote add origin "https://github.com/microsoft/mimalloc.git"
}
Invoke-Git -C $dir fetch -q --depth 1 origin $commit
Invoke-Git -C $dir checkout -q --force FETCH_HEAD
foreach ($f in @("include\mimalloc.h", "src\static.c")) {
    if (-not (Test-Path -LiteralPath (Join-Path $dir $f))) { throw "mimalloc incomplete after download: $f missing" }
}
Write-Host "mimalloc: $dir"
