# Builds Kim Walisch's primesieve (see credits\README.md) from source as a
# static library in  third_party\primesieve\install.  MSYS2 has no primesieve
# package, so build.ps1 runs this by itself when primesieve is not found.
# Needs git and, in MSYS2:  pacman -S mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja
param([string]$Msys2Root = "C:\msys64")
$ErrorActionPreference = "Stop"

$version = "v12.0"                      # the version the Linux builds were tested with
$here = $PSScriptRoot
$dest = Join-Path $here "primesieve"
$src = Join-Path $dest "src"
$bld = Join-Path $dest "build"
$inst = Join-Path $dest "install"

$mingwBin = Join-Path $Msys2Root "mingw64\bin"
$cmake = Join-Path $mingwBin "cmake.exe"
$ninja = Join-Path $mingwBin "ninja.exe"
foreach ($t in @($cmake, $ninja)) {
    if (-not (Test-Path -LiteralPath $t)) {
        throw "$t not found.  In the MSYS2 MINGW64 shell run:  pacman -S mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja"
    }
}
$env:PATH = "$mingwBin;$(Join-Path $Msys2Root 'usr\bin');$env:PATH"

$git = (Get-Command git -ErrorAction SilentlyContinue).Source
if (-not $git) { throw "git not found: install Git for Windows, or in MSYS2 run  pacman -S git" }

function Invoke-Tool {
    param([string]$exe, [string[]]$argList)
    & $exe @argList
    if ($LASTEXITCODE -ne 0) { throw "$exe $($argList -join ' ') failed" }
}

Write-Host "building primesieve $version (static library)..."
if (Test-Path -LiteralPath $dest) { Remove-Item -LiteralPath $dest -Recurse -Force }
Invoke-Tool $git @("clone", "-q", "--depth", "1", "-b", $version, "https://github.com/kimwalisch/primesieve.git", $src)
Invoke-Tool $cmake @("-S", $src, "-B", $bld, "-G", "Ninja",
    "-DCMAKE_BUILD_TYPE=Release",
    "-DCMAKE_C_COMPILER=$(Join-Path $mingwBin 'gcc.exe')",
    "-DCMAKE_CXX_COMPILER=$(Join-Path $mingwBin 'g++.exe')",
    "-DCMAKE_MAKE_PROGRAM=$ninja",
    "-DBUILD_SHARED_LIBS=OFF", "-DBUILD_STATIC_LIBS=ON", "-DBUILD_PRIMESIEVE=OFF",
    "-DCMAKE_INSTALL_PREFIX=$inst")
Invoke-Tool $cmake @("--build", $bld)
Invoke-Tool $cmake @("--install", $bld)
Copy-Item -LiteralPath (Join-Path $src "COPYING") -Destination (Join-Path $dest "LICENSE") -Force
if (-not (Test-Path -LiteralPath (Join-Path $inst "include\primesieve.hpp"))) { throw "primesieve install incomplete" }
Write-Host "primesieve: $inst"
