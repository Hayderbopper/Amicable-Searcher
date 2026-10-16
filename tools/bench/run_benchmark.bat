@echo off
rem Old build vs new build on 6 threads: times every run in bench\suites.txt
rem three times and checks that both builds find exactly the same pairs.
rem Extra options are passed on, e.g.  run_benchmark.bat -Threads 12 -Repeats 5
cd /d "%~dp0"
set "PATH=%~dp0dlls;%PATH%"
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0bench\bench.ps1" -Old "%~dp0old" -New "%~dp0new" -Threads 6 %*
echo.
pause
