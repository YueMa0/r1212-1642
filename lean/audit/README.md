# Building and auditing the Lean proof

All commands are run from lean/.

| File | Purpose |
|---|---|
| build_r1212.sh [-j N] | fetch the Mathlib cache, build the eight H01Branch modules in batches (see Memory), build the default target including R1212.Main, print the axioms |
| jobs.sh | chooses the batch size for build_r1212.sh and leanchecker_r1212.sh |
| AxiomAuditR1212.lean | `#print axioms` for the final theorem and its main steps: `lake env lean audit/AxiomAuditR1212.lean` |
| AxiomAuditRStar.lean | the same for rule R* (`rstar_isRamseyFree`) |
| DependencyModules.lean | lists the modules of this repository whose constants the final theorem uses |
| leanchecker_r1212.sh [-j N] | leanchecker replay of the 23 new modules plus a control: the H01Branch modules in batches, the others one per run |
| leanchecker_upstream.sh | require successful enumeration matching upstream_modules.txt exactly, then replay all 43 upstream modules one per run |
| sources.sha256 | SHA-256 of the new Lean sources, integration entry points and generator |
| nanoda/ | the check with nanoda, an independent kernel |

Comments in lean/RamseyIncrement/ThirdConnector/ cite the report by its earlier file name, 02_expert_report.md. The sections they cite are unchanged in report/r1212_report.md. The mathematical Lean modules are left exactly as they were audited. The root entry point and default axiom audit now also include the final R1212 theorem; UPSTREAM.md records those integration changes. sources.sha256 tracks the unchanged new mathematical modules and the current generator; its I/O fixes do not change any generated Lean text.

The default library build now reaches R1212.Main. On a fresh checkout, use build_r1212.sh to compile the large branches in batches before building that target. The lightweight CI checks audit coverage and failure handling with a fake Lake command; it does not claim a fresh Lean kernel replay.

## Memory

Each H01Branch module needs up to about 7 GB in the Lean kernel, during both compilation and replay. Lake compiles independent modules in parallel and leanchecker replays the modules it is given in parallel, and neither can be told how many to run at once. With 16 GB of memory, running all eight branch modules at once made the machine swap heavily.

So build_r1212.sh and leanchecker_r1212.sh handle the branch modules in batches of N:

- N = (physical memory in GB − 4) / 7, rounded down and kept between 1 and 8. That is 1 with 16 GB, 2 with 24 GB, 4 with 32 GB and 8 with 64 GB. The memory is read from /proc/meminfo, or from `sysctl hw.memsize` on macOS; if neither works, N = 1.
- `-j N` or `R1212_JOBS=N` sets N by hand; values above 8 count as 8.
- The other modules are much smaller, and Lake builds them in parallel as usual.

## Logs (lean/audit/logs/)

These are from runs on 29 October 2026, on an Apple M4 Mac mini with 16 GB of memory.

| Log | Contents |
|---|---|
| axioms.log | output of AxiomAuditR1212.lean: every theorem depends only on propext, Classical.choice, Quot.sound |
| build_branches.log | build time and approximate peak memory of H01Branch1 to H01Branch7 (H01Branch0: 101 s, about 6 GB) |
| leanchecker.log | replay of the 15 R1212 modules: all exit 0. The last line is a control: a missing module exits 1 |
| leanchecker_thirdconnector.log | replay of the 8 ThirdConnector modules: empty, so no errors |
| leanchecker_author.log | replay of the 43 upstream modules: all exit 0 |
| dependency_modules.log | the final theorem uses 30,595 constants (with Mathlib), from 54 modules of this repository: 15 in R1212, 8 in ThirdConnector, 31 of Tatarevic's |

The runs used the same sources as this repository; see sources.sha256.
