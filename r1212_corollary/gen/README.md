# Generator of the R1212 data tables

gen_h01.py writes lean/RamseyIncrement/R1212/H01Data.lean, H01Branch0.lean to H01Branch7.lean and H01NoK8.lean:

```bash
python3 gen_h01.py ../../lean/RamseyIncrement/R1212
```

Output is explicitly UTF-8 with LF newlines, including on Windows. The generator stages and backs up the complete batch before atomically replacing individual files. A caught write/replacement error rolls the batch back; if rollback itself fails, the error identifies the retained recovery directory. This is not a transaction across a process crash or power loss. Run only one generator per output directory.

- The tables are the 198 common neighbours of 0 and 1 in the Paley graph P₇₉₇, their positions, and their adjacency rows as bitsets.
- The search is split into 148 top-level branches, spread over 8 files so that each file needs at most a few GB in the Lean kernel.
- search_model.py is a Python model of the Lean search in lean/RamseyIncrement/R1212/Search.lean, used to compute the branches.

The generator does not need to be trusted. Lean checks the tables against Euler's criterion (`rowH_spec`, `idx_spec`), checks that the branch list is a permutation of the branches the search visits (`h01_args_perm`), and runs the search on every branch.
