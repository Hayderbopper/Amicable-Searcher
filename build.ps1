# Windows build (MSYS2 MinGW-w64): makes Build\multi_k_searcher.exe (one
# program; config.txt "mode" picks range, single or skipped) and
# Build\collect_results.exe.  (build.sh is the Linux build of the same sources.)
#
#   .\build.ps1                      fastest build, tuned for THIS machine's CPU
#   .\build.ps1 -Portable            generic x86-64-v2 build for any x86-64 CPU
#                                    from about 2009 on
#   .\build.ps1 -Clean               delete the object files first
#   .\build.ps1 -NoClangFactoring    compile external_factoring.cpp with g++ too
#                                    (only if clang++ cannot be installed)
#   .\build.ps1 -Msys2Root D:\msys64 MSYS2 somewhere else than C:\msys64
#
# One-time setup: install MSYS2 (https://www.msys2.org), open "MSYS2 MINGW64"
# and run
#   pacman -S --needed git mingw-w64-x86_64-gcc mingw-w64-x86_64-clang mingw-w64-x86_64-gmp mingw-w64-x86_64-mpfr mingw-w64-x86_64-flint mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja
# The hurchalla factoring headers are downloaded into third_party\hurchalla
# the first time (third_party\get_hurchalla.ps1, needs git), or set
# $env:HURCHALLA_INCLUDE to a folder that has them.  MSYS2 has no primesieve
# package: the first build also compiles it into third_party\primesieve
# (third_party\get_primesieve.ps1, with MSYS2's cmake and ninja).
#
# Clang factoring (on by default): external_factoring.cpp (hurchalla's
# factoring) is compiled with clang++, everything else with g++.  With GCC
# 14-16 the factoring code is about 25-35% faster when clang compiles it.  The
# file's interface passes no __int128 by value, so the two compilers' objects
# link safely.
#
# The programs need the MinGW DLLs (GMP, FLINT, primesieve, ...): run them from
# the "MSYS2 MINGW64" shell or with <Msys2Root>\mingw64\bin on PATH.  The build
# also copies those DLLs into Build\ so the folder runs on its own.
param(
    [switch]$Portable,
    [switch]$Clean,
    [switch]$NoClangFactoring,
    [string]$Msys2Root = "C:\msys64"
)
$ErrorActionPreference = "Stop"

$root = $PSScriptRoot
$srcDir = Join-Path $root "Source"
$buildDir = Join-Path $root "Build"
New-Item -ItemType Directory -Force -Path $buildDir, (Join-Path $root "Data") | Out-Null

$mingw = Join-Path $Msys2Root "mingw64"
$mingwBin = Join-Path $mingw "bin"
$gpp = Join-Path $mingwBin "g++.exe"
$clangpp = Join-Path $mingwBin "clang++.exe"
$pacman = "pacman -S --needed git mingw-w64-x86_64-gcc mingw-w64-x86_64-clang mingw-w64-x86_64-gmp mingw-w64-x86_64-mpfr mingw-w64-x86_64-flint mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja"
if (-not (Test-Path -LiteralPath $gpp)) {
    throw "g++ not found at $gpp.  Install MSYS2 and, in the MSYS2 MINGW64 shell, run:`n  $pacman`n(or pass -Msys2Root if MSYS2 is not in C:\msys64)"
}
if (-not $NoClangFactoring -and -not (Test-Path -LiteralPath $clangpp)) {
    throw "clang++ not found at $clangpp.  The factoring code is compiled with clang by default.`nIn the MSYS2 MINGW64 shell run:  pacman -S mingw-w64-x86_64-clang`nor build without it:  .\build.ps1 -NoClangFactoring"
}
# g++ and clang++ find their own DLLs and helper programs through PATH
$env:PATH = "$mingwBin;$(Join-Path $Msys2Root 'usr\bin');$env:PATH"

# ---------------------------------------------------------------- hurchalla
function Find-Hurchalla {
    $dirs = @($env:HURCHALLA_INCLUDE,
              (Join-Path $root "third_party\hurchalla\include"),
              (Join-Path $root "..\third_party\hurchalla\include"),
              (Join-Path $Msys2Root "tmp\hbench\install\include"),
              (Join-Path $mingw "include"))
    foreach ($d in $dirs) {
        if ($d -and (Test-Path -LiteralPath (Join-Path $d "hurchalla\factoring\factorize.h"))) {
            return (Resolve-Path -LiteralPath $d).Path
        }
    }
    return $null
}
$hb = Find-Hurchalla
if (-not $hb) {
    Write-Host "hurchalla factoring headers not found; downloading them (third_party\get_hurchalla.ps1)"
    & (Join-Path $root "third_party\get_hurchalla.ps1")
    $hb = Find-Hurchalla
    if (-not $hb) { throw "hurchalla headers still not found after the download" }
}
Write-Host "hurchalla: $hb"

# ---------------------------------------------------------------- flags
if ($Portable) { $cpu = @("-march=x86-64-v2", "-mtune=generic"); $objName = "obj-portable" }
else           { $cpu = @("-march=native", "-mtune=native");     $objName = "obj-native" }

# -Wa,-muse-unaligned-vector-move: 64-bit Windows only guarantees 16-byte stack
# alignment, so AVX/AVX-512 code built by MinGW GCC can crash on an "aligned"
# 32/64-byte stack access (GCC bug 54412).  This makes every such move the
# unaligned form, which costs nothing on AVX-512 CPUs.
$flags = @("-O3", "-DNDEBUG", "-std=c++20", "-pthread") + $cpu + @(
    "-Wa,-muse-unaligned-vector-move",
    "-DAMICABLE_USE_FLINT",
    "-I$srcDir",
    "-I$hb",
    "-I$(Join-Path $mingw 'include')"
)
$libs = @("-L$(Join-Path $mingw 'lib')")
# primesieve: MSYS2 has no package for it, so it is built from source into
# third_party\primesieve (third_party\get_primesieve.ps1) unless one is found
function Find-Primesieve {
    $tp = Join-Path $root "third_party\primesieve\install"
    if (Test-Path -LiteralPath (Join-Path $tp "include\primesieve.hpp")) { return @((Join-Path $tp "include"), (Join-Path $tp "lib")) }
    $old = Join-Path $Msys2Root "tmp\primesieve"         # built by hand (older setups)
    if (Test-Path -LiteralPath (Join-Path $old "include\primesieve.hpp")) { return @((Join-Path $old "include"), (Join-Path $old "build")) }
    if (Test-Path -LiteralPath (Join-Path $mingw "include\primesieve.hpp")) { return @($null, $null) }
    return $null
}
$ps = Find-Primesieve
if ($null -eq $ps) {
    Write-Host "primesieve not found; building it from source (third_party\get_primesieve.ps1)"
    & (Join-Path $root "third_party\get_primesieve.ps1") -Msys2Root $Msys2Root
    $ps = Find-Primesieve
    if ($null -eq $ps) { throw "primesieve still not found after building it" }
}
if ($ps[0]) {
    Write-Host "primesieve: $($ps[0])"
    $flags += "-I$($ps[0])"
    $libs = @("-L$($ps[1])") + $libs
}
$libs += @("-lprimesieve", "-lflint", "-lmpfr", "-lgmpxx", "-lgmp")
# clang realigns the stack for AVX itself (GCC bug 54412 is GCC's) and has no
# GNU as option: the same flags without -Wa,-muse-unaligned-vector-move
$clangFlags = $flags | Where-Object { $_ -ne "-Wa,-muse-unaligned-vector-move" }

$factoringCompiler = $gpp
if (-not $NoClangFactoring) { $factoringCompiler = $clangpp }
Write-Host "compiler : $gpp"
Write-Host "factoring: $factoringCompiler"
Write-Host "mode     : $(if ($Portable) { 'portable' } else { 'native' }) ($($cpu -join ' '))"

# ---------------------------------------------------------------- compile
$objDir = Join-Path $buildDir $objName
if ($Clean -and (Test-Path -LiteralPath $objDir)) { Remove-Item -LiteralPath $objDir -Recurse -Force }
New-Item -ItemType Directory -Force -Path $objDir | Out-Null

# rebuild everything when the compilers or flags change
$sig = "$gpp $factoringCompiler $($flags -join ' ')"
$sigFile = Join-Path $objDir "flags.txt"
if (-not (Test-Path -LiteralPath $sigFile) -or (Get-Content -LiteralPath $sigFile -Raw) -ne $sig) {
    Get-ChildItem -LiteralPath $objDir -Filter *.o | Remove-Item -Force
    Set-Content -LiteralPath $sigFile -Value $sig -NoNewline
}
$newestHeader = (Get-ChildItem -LiteralPath $srcDir -Filter *.h | Sort-Object LastWriteTime -Descending | Select-Object -First 1).LastWriteTime

$sources = Get-ChildItem -LiteralPath $srcDir -Filter *.cpp | Sort-Object Name
$common = @()
foreach ($src in $sources) {
    $obj = Join-Path $objDir ($src.BaseName + ".o")
    if (-not $src.Name.EndsWith("_main.cpp")) { $common += $obj }
    if ((Test-Path -LiteralPath $obj) -and
        (Get-Item -LiteralPath $obj).LastWriteTime -gt $src.LastWriteTime -and
        (Get-Item -LiteralPath $obj).LastWriteTime -gt $newestHeader) { continue }
    Write-Host "Compiling $($src.Name)"
    if ($src.Name -eq "external_factoring.cpp" -and -not $NoClangFactoring) {
        & $clangpp @clangFlags -c $src.FullName -o $obj
    } else {
        & $gpp @flags -c $src.FullName -o $obj
    }
    if ($LASTEXITCODE -ne 0) { throw "compile failed: $($src.Name)" }
}

# ---------------------------------------------------------------- link
# multi_k_searcher.exe (the search) and collect_results.exe (all pairs in one file)
foreach ($prog in @(@("multi_k", "multi_k_searcher.exe"), @("collect_results", "collect_results.exe"))) {
    $main = Join-Path $objDir "$($prog[0])_main.o"
    $exe = Join-Path $buildDir $prog[1]
    Write-Host "Linking $($prog[1])"
    & $gpp @flags $main @common @libs -o $exe
    if ($LASTEXITCODE -ne 0) {
        throw "$($prog[1]) build failed with exit code $LASTEXITCODE (if it says 'Permission denied', that program is still running: close it and build again)"
    }
    Write-Host "Built $exe"
}

# ---------------------------------------------------------------- DLLs
# copy the MinGW DLLs the programs load (and the DLLs those load) next to them
$objdump = Join-Path $mingwBin "objdump.exe"
if (Test-Path -LiteralPath $objdump) {
    $todo = New-Object System.Collections.Generic.Queue[string]
    $seen = @{}
    foreach ($p in @("multi_k_searcher.exe", "collect_results.exe")) { $todo.Enqueue((Join-Path $buildDir $p)) }
    while ($todo.Count -gt 0) {
        $file = $todo.Dequeue()
        foreach ($line in (& $objdump -p $file)) {
            if ($line -match "DLL Name:\s*(\S+)") {
                $name = $Matches[1]
                if ($seen.ContainsKey($name.ToLower())) { continue }
                $seen[$name.ToLower()] = $true
                $dll = Join-Path $mingwBin $name
                if (Test-Path -LiteralPath $dll) {        # Windows' own DLLs are not in mingw64\bin
                    Copy-Item -LiteralPath $dll -Destination $buildDir -Force
                    $todo.Enqueue($dll)
                }
            }
        }
    }
    Write-Host "Copied the MinGW DLLs into $buildDir"
}

Write-Host ""
Write-Host "Done.  Try:  .\Build\multi_k_searcher.exe --help    (all pairs in one file: .\Build\collect_results.exe)"
