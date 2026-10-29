import RamseyIncrement.R1212.Main
open Lean Elab Command

-- Modules of this repository whose constants `r1212_lower_bound` uses, transitively.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`RamseyIncrement.R1212.r1212_lower_bound]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do
        unless seen.contains c do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless seen.contains c do todo := todo.push c
  let mut mods : NameSet := {}
  for n in seen do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`RamseyIncrement).isPrefixOf m then mods := mods.insert m
  let ms := mods.toList.map toString |>.toArray.qsort (· < ·)
  logInfo m!"constants reached: {seen.size}\nrepository modules used: {ms.size}\n{String.intercalate "\n" ms.toList}"
