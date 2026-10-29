# Independent kernel check with nanoda

[nanoda](https://github.com/ammkrn/nanoda_lib) is a type checker for Lean 4 written independently of Lean, in Rust. It does its big-integer arithmetic with num-bigint rather than GMP and does not use the Lean runtime. It checks the export of `RamseyIncrement.R1212.r1212_lower_bound` together with every constant it uses, Mathlib included.

## Versions

- lean4export: tag v4.32.2 (commit 86e4a33), with its lean-toolchain changed to leanprover/lean4:v4.32.1, built with that toolchain.
- nanoda_lib: commit d0a02cc (2026-10-27, version 0.4.30), built with `cargo build --release --locked`; its 54 tests pass (logs/nanoda_cargo_test.log).

## Running it

```bash
LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin lean/audit/nanoda/run_nanoda.sh
```

The export is about 184 MB. The configuration (configs/full.json) turns on nanoda's Nat and String extensions and permits only the axioms propext, Classical.choice and Quot.sound; any other axiom is an error. It also prints the theorem and the definitions in its statement, so that the statement can be compared with the source.

## Results (29 October 2026, Apple M4, 16 GB)

| Check | Declarations | Result | Threads | Time | Peak memory |
|---|---:|---|---:|---:|---:|
| H01Branch0 only (`h01_chunk_0_ok`) | 729 | no errors | 4 | 45 s | 9.6 GB |
| **r1212_lower_bound, complete** | **31,106** | **no errors** | 2 | 320 s | 10.5 GB |
| control: `rowH_spec` as exported | 661 | no errors | 1 | 12 s | 5.0 GB |
| control: `rowH_spec` with the literal 398 changed to 399 | — | **rejected**: `assertion failed: self.def_eq(u, v)`, exit code 101 | 1 | 2 s | — |

- logs/full.log is the output of the complete check. It prints the statement as `LE.le (OfNat.ofNat 1642) (RamseyIncrement.ramseyNumber (OfNat.ofNat 12) (OfNat.ofNat 12))`, and the definitions of ramseyNumber, ForcesRamsey, HasRamseyColoring, IsRamseyFree, SimpleGraph.CliqueFree, IsNClique and IsClique.
- In the control, 398 is the exponent in Euler's criterion. The changed literal occurs once in the export and is used only by `qrB`, the quadratic-residue test. The rejection shows that nanoda actually performs the kernel computations of the proof.
- SHA-256 of the complete export used here: 1b44f55774042c07f717d85dbc04c95478f21ecf4dfc762f26e085e38f110b58.
