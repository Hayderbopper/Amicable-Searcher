Amicable-Searcher benchmark kit
===============================

old\   the program before this change
new\   the program with this change
bench\ the benchmark script (bench.ps1) and the list of runs (suites.txt)

To run it, double-click run_benchmark.bat (or run it from a command prompt).
It uses 6 threads, runs each test 3 times per program, alternating old and
new, and reports the median time of each.  It also checks that both programs
find exactly the same pairs in every run; the last column says so.  The whole
thing takes a few minutes.  Close other heavy programs first for steady times.

Options (add them after run_benchmark.bat):
  -Threads 12     use 12 threads instead of 6
  -Repeats 5      5 runs per test instead of 3

The report is printed and saved as bench\bench_report.txt.  Nothing outside
this folder and your temporary folder is touched; the work folders are
deleted at the end.

Both programs are generic x86-64-v2 builds (the same kind as the release
downloads).  A build made on your own PC with build.ps1 is tuned for your CPU
and somewhat faster, but the old/new comparison is the same.
