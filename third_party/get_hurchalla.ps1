# Downloads Jeffrey Hurchalla's header-only factoring library (see
# hurchalla\LICENSE) at the commits this project was tested with and puts its
# headers in  third_party\hurchalla\include.  build.ps1 runs this by itself
# when the headers are missing.  Needs git (Git for Windows, or MSYS2's git).
$ErrorActionPreference = "Stop"

$here = $PSScriptRoot
$dest = Join-Path $here "hurchalla"

# factoring pins the other two (see its CMakeLists.txt)
$repos = @(
    @("factoring",          "a1dfea9e38daab9e25ba7c0f1b38af1959fbdd6a"),
    @("modular_arithmetic", "cb5e74a154dc665ffd50ab04348677e596dd362a"),
    @("util",               "9163344ee69f21a21cb8928dd30fc2ff15e94f0c")
)

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

Write-Host "fetching hurchalla factoring, modular_arithmetic and util..."
foreach ($r in $repos) {
    $dir = Join-Path $dest "src\$($r[0])"
    if (-not (Test-Path -LiteralPath (Join-Path $dir ".git"))) {
        if (Test-Path -LiteralPath $dir) { Remove-Item -LiteralPath $dir -Recurse -Force }
        Invoke-Git init -q $dir
        Invoke-Git -C $dir remote add origin "https://github.com/hurchalla/$($r[0]).git"
    }
    Invoke-Git -C $dir fetch -q --depth 1 origin $r[1]
    Invoke-Git -C $dir checkout -q --force FETCH_HEAD
}

$inc = Join-Path $dest "include"
if (Test-Path -LiteralPath $inc) { Remove-Item -LiteralPath $inc -Recurse -Force }
New-Item -ItemType Directory -Force -Path $inc | Out-Null
foreach ($sub in @("factoring\include",
                   "modular_arithmetic\modular_arithmetic\include",
                   "modular_arithmetic\montgomery_arithmetic\include",
                   "util\include")) {
    Copy-Item -Path (Join-Path (Join-Path $dest "src") "$sub\*") -Destination $inc -Recurse -Force
}
Copy-Item -LiteralPath (Join-Path $dest "src\factoring\LICENSE") -Destination (Join-Path $dest "LICENSE") -Force
foreach ($h in @("hurchalla\factoring\factorize.h", "hurchalla\util\programming_by_contract.h")) {
    if (-not (Test-Path -LiteralPath (Join-Path $inc $h))) { throw "headers incomplete after download: $h missing" }
}
Write-Host "hurchalla headers: $inc"
