# Independent review of bruteforce_kclique.c

Done on 29 October 2026 by a separate review agent (Claude Opus 5.5, Anthropic), started from the main session. It was given only the paths of the program, the colouring and the output, and a description of the task, not the main agent's conclusions. What follows is an edited version of its report; the programs and tests in this directory were written by it. Translated from the Chinese original.

## 1. The algorithm as the reviewer reads it

- Input: reads the non-empty lines and strips \r and \n; requires every line to have as many characters as there are lines; the character '1' is red (1) and anything else is 0. Exits if the diagonal is non-zero or the matrix is not symmetric.
- Task list: for every v in [v_lo, v_hi) (with v < n) and every colour c ∈ {0,1} that OUT does not record as finished, it queues (v, c, m), where m = |{w > v : A[v][w] = c}|; m > 1024 is an error. Tasks are sorted by m in decreasing order, and threads take them with an atomic counter.
- Each task (run_task): lists P(v,c) in increasing w, then renumbers it by decreasing c-colour degree inside P (stable sort). Each vertex has a bitset of 64-bit words recording its c-coloured neighbours in P, itself excluded. If m ≥ t−1, it calls expand on the whole of P.
- Search (expand): first partitions the candidate set greedily into independent sets (colour classes), then branches from the highest colour class down:
  - returns when depth + col[i] < t−1;
  - reports a find when depth+1 = t−1;
  - otherwise recurses if P ∩ N(v) is non-empty, then removes v from P.
- Witnesses and output: a clique that is found is mapped back to the original numbering, v is prepended, and every pair is re-checked against A. Each task writes one line of JSON under a mutex and flushes.

## 2. Conclusion

**No defect was found that could make this run's conclusion, "no monochromatic K12", wrong.**
- Checked section by section against the code, the search, the construction of P(v,c), the input parsing and the task queue are correct.
- The binary that was run is byte-for-byte identical to the output of `clang -O3` on this source.
- The input file is well formed.
- Each of the 3282 tasks was searched completely, exactly once, in a single run.
- The reviewer wrote a separate search program that shares no code with the original (indep3c.c). On 1486 tasks this program also returns "none", with exactly the node counts in the log, including the largest task (v=0, c=0, |P|=822).

## 3. Issues found (none was triggered by this run)

- **D1: resuming looks only at the start of a line (lines 207–217).**
  - A line that starts with `{"v":V,"c":C` and does not contain "timeout" marks (v,c) as finished. The program does not check that the line is complete, that the result is none or found, or that it comes from the same graph and the same t; the output records neither t nor the graph's hash.
  - The reviewer demonstrated two ways this goes wrong:
    - If OUT ends with a truncated line `{"v":5,"c":1,"m":2` (for example after the process is killed, or the disk fills up in the middle of a write), task (5,1) is never searched. The program reports found=13 (it should be 14) and still exits with 0.
    - Resuming a run with t=8 from the OUT of a run with t=9, the program reports tasks=0, found=0, although 14 tasks in fact contain a K8.
  - The "finished:" statistics printed at the end count only the current invocation.
  - This run is not affected:
    - run.log says tasks=3282, so no task was skipped;
    - the output has exactly 3282 well-formed lines, one per (v,c);
    - the order of the lines matches a fresh task queue: each line's position in the queue is at most its line number plus 7;
    - node counts depend on t: rerunning 20 sampled tasks with t=11 or t=13 changes every node count, and rerunning them with t=12 reproduces the log exactly.
- **D2: weak input checks (lines 190, 196, 199).**
  - Every character other than '1' counts as 0: a file with every '0' replaced by 'x' is accepted (demonstrated).
  - Empty lines are skipped silently.
  - An empty file gives n=0 and 0 tasks, exits with 0, and prints "found=0 timeout=0".
  - n is not compared with the expected number of vertices.
  - This run is not affected: the file contains only the bytes '0', '1' and '\n', in 1641 lines of 1641 characters, with no CR and no BOM; it is symmetric with zero diagonal, its SHA-256 matches the record, and the log says n=1641.
- **D3: command-line arguments are not checked (lines 176–183, 233–235).**
  - With threads=0 nothing runs, nothing is written, and the exit code is 0 (demonstrated).
  - threads > 256 overruns th[256].
  - t > 64 overruns the three 64-entry arrays cur, wit and g; t ≤ 1 makes no sense.
  - atoi accepts any string.
  - With exactly 6 arguments, v_lo is ignored and the full range is used (the safe direction).
  - This run is not affected: t=12, 8 threads, full range, node_cap=0.
- **D4: the witness re-check is incomplete (lines 136–147).**
  - It checks only the colour of each pair, not that the t vertices are distinct or that they are all greater than v. For c=0 a repeated vertex would pass, since A[u][u]=0.
  - The search itself cannot produce repeated vertices: the bitsets exclude the vertex itself, and v is not in P. A witness that fails the re-check is still reported as found, which is the safe direction.
  - So this affects only the independence of the re-check, not the "none" results.
- **D5: I/O and memory-allocation errors are not handled (lines 150–152, 236, 157, 187, 196, 218, 234).**
  - The return values of fprintf, fflush and fclose are not checked: with a full disk, lines would be lost and the exit code would still be 0.
  - Failures of malloc and pthread_create are not checked either, but such failures only crash the program; they cannot produce a wrong conclusion.
  - This run is not affected: the output is complete.

Harmless style issues:
- No warnings with `-Wall -Wextra`; `-Wsign-conversion` gives 24, none of which can meet a negative value.
- `done[v][c&1]` does not check the range of c.
- node_cap=0 means no limit; a negative value times out at once, which is the safe direction.

## 4. What the reviewer could not verify

- Of the 1796 tasks with v < 900, only 4 large ones were rerun. These tasks account for 99.4% of all nodes and CPU time. For them the evidence is the code analysis, the identity of binary and source, and the complete record of one run. A transient hardware or system fault during the original run can only be excluded by rerunning everything: about 15 CPU-hours, preferably with the independent implementation (indep3c.c) and on another machine.
- Whether the graph is the intended construction: the reviewer checked only its format and hash.
- Uninitialised memory: MemorySanitizer is not available on macOS. This point rests on the code inspection, and on node counts being identical across different builds.

## 5. Tests the reviewer ran

About 7.5 CPU-minutes in total, at most 2 threads, all in a temporary directory.

1. Recompilation: the source compiled with `clang -O3` is byte-for-byte identical to the binary that was run (37720b55…).
2. The graph file (numpy): only the bytes '0', '1' and '\n'; 1641 × 1641, symmetric, zero diagonal.
3. The output file:
   - 3282 lines, all valid JSON, all results none, each (v,c) exactly once;
   - the m on every line equals an independently computed |P(v,c)|;
   - the 3233 tasks with m ≥ 11 have nodes ≥ 1, and the 49 tasks with m < 11 have nodes = 0;
   - the order of the lines is consistent with a single run; the total node count is 1.888e11.
4. White-box tests (whitebox.c includes the reviewed source unchanged):
   - expand called directly on 480 graphs, m from 20 to 1024, with cliques planted near bit positions 62–65, 126–129, 255/256, 511/512 and the last bit;
   - run_task called for every (v,c) on 8 random colourings per seed, n from 130 to 350, t from 9 to 12;
   - 4 seeds in all, 0 errors; also 0 errors under AddressSanitizer and UndefinedBehaviorSanitizer.
5. The actual binary against networkx, task by task (blackbox.py):
   - 12 random colourings, n from 70 to 210, t chosen near the clique number, 2 threads;
   - the inputs include CRLF line endings, a missing final newline and extra empty lines at the end;
   - 0 disagreements in 3442 tasks: 85 found (23 of them needing more than one 64-bit word) and 3357 none (558 of them spanning several words); all witnesses valid.
6. The actual binary rerun on the real graph:
   - for the 1282 tasks with v ≥ 1000, m, the results and the node counts all agree with the log;
   - builds with ThreadSanitizer and with AddressSanitizer/UndefinedBehaviorSanitizer, run on the 782 tasks with v ≥ 1250, report nothing and give the same node counts.
7. Sensitivity to t: rerunning the 20 tasks with v = 1100–1109 with t=11 or t=13 gives node counts that all differ from the log (t=12). With t=11 all 20 tasks find a valid monochromatic K11, which is also a positive control on the real graph.
8. Three independent implementations, sharing no code with the original program and using 32-bit words:
   - indep_kclique.c: sequential enumeration with only the vertex-count bound;
   - indep2.c: a colouring-bound search written from scratch;
   - indep3c.c: like indep2, but with the same vertex ordering rule as the original program.
   - On 3784 synthetic tasks the three agree with each other and with results verified by networkx: 0 disagreements.
   - On the real graph:
     - indep_kclique and indep2 return none on the 682 tasks with v ≥ 1300;
     - indep3c returns none on the 1482 tasks with v ≥ 900 (largest m 374), with exactly the node counts in the log;
     - on four large tasks, indep3c's node counts also equal the log exactly:

       | Task (v, c) | m | Nodes |
       |---|---:|---:|
       | (639, 0) | 504 | 10,225,057 |
       | (435, 0) | 600 | 39,349,428 |
       | (258, 0) | 702 | 139,106,636 |
       | (0, 0) | 822 | 539,188,066 |

     - Identical node counts mean that the two programs walk the same search tree.
9. D1–D3 were demonstrated on a 60-vertex graph with a planted clique, with the results described above.

Note: when whitebox.c was copied here, its `#include` path was changed to `../../bruteforce_kclique.c`, so that it points at the program in this repository; the other files were copied unchanged.
