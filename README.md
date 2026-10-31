# R(12,12) ≥ 1642

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23770924.svg)](https://doi.org/10.5281/zenodo.23770924)

> **Update, 30 October 2026:** a newer colouring gives R(12,12) ≥ 1658 ([r1212-1658](https://github.com/YueMa0/r1212-1658)); it is computer-verified, but has no Lean proof.

This repository contains a red/blue colouring of the complete graph K₁₆₄₁ with no monochromatic K₁₂, and a Lean 4 proof that R(12,12) ≥ 1642.

To our knowledge this improves the best published lower bound, R(12,12) ≥ 1641 (M. Tatarevic, [arXiv:2608.06531](https://arxiv.org/abs/2608.06531), August 2026). The literature search was made on 29 October 2026. The result has not been peer reviewed.

## The result

```lean
theorem RamseyIncrement.R1212.r1212_lower_bound : 1642 ≤ ramseyNumber 12 12
```

- `ramseyNumber k s` is the least n such that every simple graph on n vertices contains a k-clique or an independent set of size s. The definition is Tatarevic's (lean/RamseyIncrement/RamseyNumber.lean).
- The colouring starts from the Mathon–Shearer (11,11)-colouring M(797) on 1596 vertices.
  - Tatarevic's two-parameter increment adds 2k + 2s = 44 vertices.
  - A new rule R* flips 7 old edges and adds one more vertex: 1596 + 44 + 1 = 1641.
- R* is a theorem for all k, s ≥ 5, under two extra conditions on the certificates, (P1) and (P2). It gives R(k+1, s+1) ≥ R(k,s) + 2k + 2s + 1 whenever a (k,s)-colouring on R(k,s) − 1 vertices has such certificates. In the tables of Radziszowski's survey *Small Ramsey Numbers*, R(12,12) is the only entry this improves.
- The construction, the rule, its colour table and a hand proof are in [report/r1212_report.md](report/r1212_report.md).

## Where to start

- **To check the mathematics**: read [graph/README.md](graph/README.md) (the colouring and its vertex order), then Sections 1–4 of [the report](report/r1212_report.md) (the construction, the rule R*, its colour table and the proof), then [lean/RamseyIncrement/R1212/Main.lean](lean/RamseyIncrement/R1212/Main.lean) (the final theorem and the certificates).
- **To check the colouring yourself**: run [verify/run_checks.sh](verify/run_checks.sh), which takes about a minute; see [Checking it yourself](#checking-it-yourself).

## How it was checked

| Check | What it establishes | Where | Cost |
|---|---|---|---|
| Lean proof, Lean 4.32.1 kernel | the theorem above, with axioms propext, Classical.choice, Quot.sound only | lean/ | the eight branch modules take about 13 min in total, 4–7 GB each |
| leanchecker | replay of the compiled proof, one module at a time | lean/audit/ | about 17 min |
| nanoda, an independent kernel written in Rust | the same proof: 31,106 declarations, no errors | lean/audit/nanoda/ | about 5 min; 11 GB |
| exhaustive clique search | no monochromatic K₁₂ in graph/r1212_1641.graph, without using any structure | verify/ | 15.3 CPU-hours |
| clone projection; rebuild from the report text | the same, using only that M(797) is an (11,11)-colouring; the file matches the report | verify/ | about 1 min |

The Lean proof does not depend on the hand proof, on the generator of its data tables, or on any of the programs in verify/. Logs of all runs are included: lean/audit/logs/, lean/audit/nanoda/logs/, verify/results/.

## How this work was done

The work was done between 27 and 29 October 2026 by Yue Ma together with Claude (Claude Opus 5.5, by Anthropic), working as an agent in Claude Code. Yue Ma chose the research direction, approved each stage of the investigation (including every download and installation) and decides how the result is published. Claude did most of the technical work: the literature search, the computer experiments that led to rule R*, the hand proof in the report, the Lean formalization and the computer checks in verify/. The code review in verify/second_check/review/ was also done by Claude, as a separate agent that was given only the program, the colouring and the outputs, not our conclusions.

No human mathematician has yet checked the hand proof line by line. The Lean proof does not depend on it.

## Checking it yourself

**The colouring.** The quick checks need Python 3 with numpy and networkx, and a C compiler:

```bash
PY=python3 verify/run_checks.sh
```

The exhaustive search takes about 15 CPU-hours (about 2 hours with 8 threads). Start it with a new output file; verify/README.md lists the program's known robustness issues.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1641.graph 12 bruteforce.jsonl 8
```

**The Lean proof.** It needs elan, about 8 GB of disk for Mathlib, and at least 16 GB of memory.

```bash
lean/audit/build_r1212.sh
lean/audit/leanchecker_r1212.sh
lean/audit/leanchecker_upstream.sh
```

The default `lake build` target now includes `RamseyIncrement.R1212.Main`, and `AxiomAudit.lean` also prints the axioms of the final lower-bound theorem. On a fresh checkout, use the build script above instead of a bare `lake build` or `lake build RamseyIncrement.R1212.Main`: Lake would compile the eight H01Branch modules in parallel, at up to 7 GB each. The script builds them in batches before building the default target, and the replay script replays them the same way.

- The batch size is chosen from the physical memory, (GB − 4) / 7, between 1 and 8: 1 module at a time with 16 GB, 4 with 32 GB, all 8 with 64 GB.
- `-j N` or `R1212_JOBS=N` sets it by hand, for example `lean/audit/build_r1212.sh -j 2`.

For nanoda, see lean/audit/nanoda/README.md.

The GitHub Actions workflow runs quick graph checks and regression tests for failed checks, generator writes and audit coverage. It does not rerun the exhaustive graph search or the memory-intensive Lean/nanoda proof checks.

## Layout

| Path | Contents |
|---|---|
| graph/ | the colouring, its SHA-256 and a description of its vertex order |
| report/ | the construction, the rule R*, the colour table, the proof and all checks |
| lean/ | Tatarevic's Lean library, unchanged, plus the new directories RamseyIncrement/ThirdConnector/ (rule R*) and RamseyIncrement/R1212/ (the corollary) |
| lean/audit/ | build and replay scripts, axiom audits, logs, the nanoda check |
| r1212_corollary/gen/ | the generator of the data tables in lean/RamseyIncrement/R1212/ |
| verify/ | the independent computer checks of the colouring, a second check of the exhaustive search (including a code review by a separate AI agent), and their outputs |

## Credits

- **Milos Tatarevic**: the two-parameter increment R(k+1, s+1) ≥ R(k,s) + 2k + 2s, its Lean formalization and the build setup ([repository](https://github.com/milostatarevic/ramsey-increment-theorem), MIT license). His 43 mathematical modules are unchanged from commit 36c15ec. The library entry point and default axiom audit were extended to include the new theorem; see [UPSTREAM.md](UPSTREAM.md).
- **New in this repository**: the rule R*, its proof and its Lean formalization; the Lean proof of R(12,12) ≥ 1642; the colouring; the checks in verify/.
- The (11,11)-colouring M(797) is due to Mathon (1987) and Shearer (1986).
- **Author**: Yue Ma. For the role of AI, see [How this work was done](#how-this-work-was-done).

## How to cite

Version 1.0.0 is archived on Zenodo: [doi:10.5281/zenodo.23770925](https://doi.org/10.5281/zenodo.23770925). To cite all versions, use [doi:10.5281/zenodo.23770924](https://doi.org/10.5281/zenodo.23770924). Citation metadata is in [CITATION.cff](CITATION.cff); GitHub shows it under "Cite this repository". Please cite Tatarevic's paper as well: M. Tatarevic, *A constructive two-parameter Ramsey increment*, [arXiv:2608.06531](https://arxiv.org/abs/2608.06531).

## License

MIT; see [LICENSE](LICENSE).
