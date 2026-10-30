# Files from Tatarevic's repository

These files are copied unchanged from https://github.com/milostatarevic/ramsey-increment-theorem, commit 36c15eca0c601be7b7f33e30ee6890f395d2e1ea (2026-08-09, "Update README.md"), directory lean/:

- lean/.gitignore, lean/lake-manifest.json, lean/lakefile.lean, lean/lean-toolchain;
- the 43 files under lean/RamseyIncrement/ outside ThirdConnector/ and R1212/.

They are covered by Tatarevic's MIT license; the copyright notice is in LICENSE.

Two additional files derive from that revision, with integration changes:

- lean/RamseyIncrement.lean additionally imports RamseyIncrement.R1212.Main so the default library target includes the new theorem.
- lean/AxiomAudit.lean additionally prints the axioms of RamseyIncrement.R1212.r1212_lower_bound.

The 43 upstream mathematical modules themselves are unchanged. Everything else is new: lean/RamseyIncrement/ThirdConnector/, lean/RamseyIncrement/R1212/, lean/audit/, and all files outside lean/.

To check that the copied files are unchanged:

```bash
git clone https://github.com/milostatarevic/ramsey-increment-theorem upstream
git -C upstream checkout 36c15eca0c601be7b7f33e30ee6890f395d2e1ea
diff -r upstream/lean lean -x .lake -x ThirdConnector -x R1212 -x audit -x RamseyIncrement.lean -x AxiomAudit.lean
```

The last command prints nothing for the unchanged files; the two integration changes are listed above.
