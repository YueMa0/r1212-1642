import RamseyIncrement.R1212.Main
open RamseyIncrement.R1212 RamseyIncrement.R1212.MV

#check @A
#check @B
#check a
#check b

/-- The candidate file's layout: 0..796 → A, 797..1593 → B, 1594 → a, 1595 → b. -/
def toMV (i : Nat) : MV :=
  if i < 797 then A (i : F)
  else if i < 1594 then B ((i - 797 : Nat) : F)
  else if i = 1594 then a else b

def idxOf : MV → Nat
  | .inl x => x.val
  | .inr (.inl y) => 797 + y.val
  | .inr (.inr false) => 1594
  | .inr (.inr true) => 1595

def row (i : Nat) : String :=
  String.ofList ((List.range 1596).map fun j ↦ if decide (mathon.Adj (toMV i) (toMV j)) then '1' else '0')

#eval show IO Unit from do
  -- the layout really is a bijection onto MV
  let ok := (List.range 1596).all fun i ↦ idxOf (toMV i) == i
  IO.println s!"layout round trip: {ok}"
  IO.println s!"C = {(List.finRange 10).map (idxOf ∘ cVec)}"
  IO.println s!"I = {(List.finRange 10).map (idxOf ∘ iVec)}"
  let path := (← IO.getEnv "OUT").getD "lean_mathon_1596.txt"
  let h ← IO.FS.Handle.mk path .write
  for i in [0:1596] do
    h.putStrLn (row i)
