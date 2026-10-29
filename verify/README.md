# Computer checks of the colouring

These programs read graph/r1212_1641.graph and use none of the Lean code. Python 3 with numpy and networkx is needed, and a C compiler.

## Quick checks (about a minute)

```bash
PY=python3 verify/run_checks.sh
```

| Script | What it checks |
|---|---|
| check_mathon.py | the first 1596 vertices are M(797); the neighbourhood lemma via explicit automorphisms and isomorphisms; the certificates (red K₁₀, blue K₁₀, Type A, (P1), (P2)) |
| maxclique.c, test_maxclique.py | an exact maximum-clique search, tested against networkx; it finds clique number 7 in both 198-vertex common neighbourhoods of P₇₉₇, so ω(P₇₉₇) = α(P₇₉₇) = 9 |
| check_projection.py | the clone projection: no monochromatic K₁₂, given that M(797) is an (11,11)-colouring. With an argument u:v it flips the edge uv; undoing any flip of R* must make the check fail |
| crosscheck_p101.py | the projection agrees with brute force on a 126-vertex instance built from the Paley graph P₁₀₁ (data/) |
| rebuild_from_report.py | rebuilds the colouring from the text of the report (Sections 1.1, 1.2, 2, Appendices A, B) and compares it byte for byte |

rebuild_from_report.py names the report by its earlier file name, 02_expert_report.md; those sections are unchanged in report/r1212_report.md.

## Exhaustive search (about 15 CPU-hours)

bruteforce_kclique.c uses no structure of the graph. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices are later vertices joined to v in its colour c. So for each v and c the program decides whether P(v,c) = {w > v : colour(v,w) = c} contains a K₁₁ of colour c. That is 3,282 tasks, each an exact bitset branch and bound.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1641.graph 12 bruteforce.jsonl 8
```

- Result on 29 October 2026 (results/bruteforce_r1212_1641.jsonl, run information in results/bruteforce_run_meta.txt): all 3,282 tasks "none", 1.888 × 10¹¹ nodes, 15.28 CPU-hours, 1 h 55 min with 8 threads on an Apple M4.
- test_bruteforce.py: agreement with networkx on 60 random colourings; the 126-vertex P₁₀₁ instance; a K₁₂ is found once the flip c_2x_0 is undone.

### Known robustness issues

An independent review by a separate AI agent (Claude), which was given only the program, the colouring and the outputs (report: second_check/review/review_report.md), found no defect that could affect the result above, and five issues that this run did not trigger:

- D1: on restart, a task counts as finished if a line of the output file merely starts with its (v, c). A truncated line, or an output file from a run with another t, makes tasks be skipped silently. **Always start with a new output file.**
- D2: every character other than '1' is read as 0, empty lines are skipped, and the number of vertices is not checked.
- D3: command-line arguments are not checked; for example, 0 threads runs nothing and exits with 0.
- D4: the re-check of a witness does not check that its vertices are distinct.
- D5: I/O errors are not checked.

The program is published unchanged, so that it matches the recorded run: same source SHA-256, and the same binary when rebuilt with the same compiler.

## Second check (second_check/)

| File | Purpose |
|---|---|
| ExportMathon.lean | evaluates the Lean definition `mathon.Adj` and writes the 1596 × 1596 matrix in the file's vertex order; it coincides with the first 1596 vertices of the file. Run from lean/ with `OUT=... lake env lean ../verify/second_check/ExportMathon.lean` |
| check_file.py | hash, format and symmetry of the file; comparison with the exported matrix; that the output covers every task once, with the right size of P(v,c) |
| controls.py | on the real graph: K₁₂s created by flipping one edge in the largest task; undoing each class of flips of R*; reruns compared with the recorded node counts |
| hidden_plant.py | K₁₂s assembled from ordinary vertices of M(797), planted into the largest tasks |
| mc_cross.py | 14 tasks rechecked with maxclique.c |
| review/ | the AI reviewer's report, its three independent implementations and its tests |

Results (results/bruteforce_second_check.log): all planted K₁₂s were found; reruns reproduce the recorded results and node counts; one independent implementation returns "none" with exactly the recorded node counts on the 1,482 tasks with v ≥ 900 and on four large tasks, including the largest. The 1,796 tasks with v < 900 (99.4% of the search) were run only once, by the original program.

## Results folder

| File | Contents |
|---|---|
| bruteforce_r1212_1641.jsonl | one line per task of the exhaustive search. The run wrote it as mathon797_1641.jsonl, the name in bruteforce_run_meta.txt; only the name has changed (SHA-256 b0211fae550183e126c179cfa80f6bab29831b4db97c4addee01a56b7c9780e7) |
| bruteforce_run_meta.txt | start and end time, SHA-256 of the graph, source and binary, compiler, command |
| bruteforce_second_check.log | output of the second check (local paths shortened) |
| quick_checks.log | output of run_checks.sh, run from this repository on 29 October 2026 (38 s) |
