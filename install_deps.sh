#!/usr/bin/env bash
# Installs what build.sh needs on Linux: g++, clang++ (the factoring code is
# compiled with clang by default), git, and the development packages of GMP,
# MPFR, FLINT and primesieve.  Uses the system package manager (sudo).
#
#   bash install_deps.sh        then   ./build.sh
set -euo pipefail

SUDO=""
if [ "$(id -u)" -ne 0 ]; then
    command -v sudo >/dev/null 2>&1 || { echo "install_deps.sh: run as root or install sudo" >&2; exit 1; }
    SUDO=sudo
fi

if command -v apt-get >/dev/null 2>&1; then
    $SUDO apt-get update
    $SUDO apt-get install -y g++ clang git libgmp-dev libmpfr-dev libflint-dev libprimesieve-dev
elif command -v dnf >/dev/null 2>&1; then
    $SUDO dnf install -y gcc-c++ clang git gmp-devel mpfr-devel flint-devel primesieve-devel
elif command -v pacman >/dev/null 2>&1; then
    $SUDO pacman -S --needed --noconfirm gcc clang git gmp mpfr flint primesieve
elif command -v zypper >/dev/null 2>&1; then
    $SUDO zypper install -y gcc-c++ clang git gmp-devel mpfr-devel flint-devel primesieve-devel
else
    echo "install_deps.sh: no apt-get, dnf, pacman or zypper found." >&2
    echo "Install by hand: a C++20 compiler, clang++, git, GMP, MPFR, FLINT (3.x) and primesieve." >&2
    exit 1
fi

echo ""
echo "Dependencies installed.  Next:  ./build.sh"
