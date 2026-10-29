/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.TypeB.Construction

/-!
# The additional Type B edge changes

This file audits both edges in (14B): their source colors in the
first-connector graph, their target colors in the edited old graph, their
non-overlap, and the exact classification of every newly red or blue edge.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private abbrev c2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.c (c2Index data)

private abbrev i2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.i (i2Index data)

private abbrev a2
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c2Index data)

private abbrev xStar
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

/-! ## Source colors -/

/-- The edge `c₂x_*` is red before the additional Type B edit. -/
theorem finalGraph_adj_c2_xStar
    (data : Certificates.PlusCaseBData G k s) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core (c2 data)) (xStar data) := by
  rw [Switching.final_adj_iff]
  left
  constructor
  · rw [Switching.preGraph_adj_lower_x_iff]
    simp [Canonical.secondCertificateAt]
  · rw [Switching.removedRedGraph_adj_iff]
    simp [Switching.SymmPair]

/-- The edge `i₂a₂` is blue before the additional Type B edit. -/
theorem finalGraph_not_adj_i2_a2
    (data : Certificates.PlusCaseBData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core (i2 data)) (a2 data) := by
  rw [Switching.final_adj_iff]
  push Not
  constructor
  · rw [Switching.preGraph_adj_lower_lower_iff,
      specialLift_adj_core_a]
    intro hci
    exact False.elim ((Set.disjoint_left.1 data.cert.disjoint)
      (Set.mem_range_self (c2Index data))
      (by
        rw [hci]
        exact Set.mem_range_self (i2Index data)))
  · rw [Switching.addedRedGraph_adj_iff]
    simp [Switching.SymmPair]

/-- Every explicitly added-red Type B edge has blue source color. -/
theorem extraBAddedRedGraph_source_blue
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraBAddedRedGraph data).Adj u v) :
    ¬(Switching.finalGraph data.cert).Adj u v := by
  rw [extraBAddedRedGraph_adj_iff] at h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact finalGraph_not_adj_i2_a2 data
  · rcases h with ⟨rfl, rfl⟩
    exact fun huv ↦
      finalGraph_not_adj_i2_a2 data
        ((Switching.finalGraph data.cert).adj_symm huv)

/-- Every explicitly removed-red Type B edge has red source color. -/
theorem extraBRemovedRedGraph_source_red
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraBRemovedRedGraph data).Adj u v) :
    (Switching.finalGraph data.cert).Adj u v := by
  rw [extraBRemovedRedGraph_adj_iff] at h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact finalGraph_adj_c2_xStar data
  · rcases h with ⟨rfl, rfl⟩
    exact (Switching.finalGraph data.cert).adj_symm
      (finalGraph_adj_c2_xStar data)

/-! ## Non-overlap and target colors -/

/-- The blue-to-red and red-to-blue Type B switch graphs are disjoint. -/
theorem extraBAddedRedGraph_disjoint_extraBRemovedRedGraph
    (data : Certificates.PlusCaseBData G k s) :
    Disjoint (extraBAddedRedGraph data)
      (extraBRemovedRedGraph data) := by
  rw [SimpleGraph.disjoint_left]
  intro u v hadd
  exact fun hrem ↦ extraBAddedRedGraph_source_blue data hadd
    (extraBRemovedRedGraph_source_red data hrem)

/-- Every explicitly added-red edge is red in the edited old graph. -/
theorem extraBOldGraph_adj_of_added
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraBAddedRedGraph data).Adj u v) :
    (extraBOldGraph data).Adj u v := by
  rw [extraBOldGraph_adj_iff]
  exact Or.inr ((extraBAddedRedGraph_adj_iff data u v).1 h)

/-- Every explicitly removed-red edge is blue in the edited old graph. -/
theorem extraBOldGraph_not_adj_of_removed
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraBRemovedRedGraph data).Adj u v) :
    ¬(extraBOldGraph data).Adj u v := by
  intro hedge
  rw [extraBOldGraph_adj_iff] at hedge
  rcases hedge with hedge | hedge
  · exact hedge.2 ((extraBRemovedRedGraph_adj_iff data u v).1 h)
  · have hadd :
        (extraBAddedRedGraph data).Adj u v :=
      (extraBAddedRedGraph_adj_iff data u v).2 hedge
    exact extraBAddedRedGraph_source_blue data hadd
      (extraBRemovedRedGraph_source_red data h)

/-- The added-red switch graph lies in the old blue graph. -/
theorem extraBAddedRedGraph_le_final_compl
    (data : Certificates.PlusCaseBData G k s) :
    extraBAddedRedGraph data ≤
      (Switching.finalGraph data.cert)ᶜ := by
  intro u v h
  exact (SimpleGraph.compl_adj _ _ _).2
    ⟨h.ne, extraBAddedRedGraph_source_blue data h⟩

/-- The removed-red switch graph lies in the old red graph. -/
theorem extraBRemovedRedGraph_le_final
    (data : Certificates.PlusCaseBData G k s) :
    extraBRemovedRedGraph data ≤
      Switching.finalGraph data.cert := by
  intro u v h
  exact extraBRemovedRedGraph_source_red data h

/-! ## Exact changed-edge classification -/

/-- Every red edge present only after the Type B edit is `i₂a₂`. -/
theorem classify_extraB_new_red_edge
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (hnew : (extraBOldGraph data).Adj u v)
    (hold : ¬(Switching.finalGraph data.cert).Adj u v) :
    extraBAddedRedRel data u v := by
  rw [extraBOldGraph_adj_iff] at hnew
  rcases hnew with hnew | hnew
  · exact False.elim (hold hnew.1)
  · exact hnew

/-- Every blue edge present only after the Type B edit is `c₂x_*`. -/
theorem classify_extraB_new_blue_edge
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (hnew : (extraBOldGraph data)ᶜ.Adj u v)
    (hold : ¬(Switching.finalGraph data.cert)ᶜ.Adj u v) :
    extraBRemovedRedRel data u v := by
  have huv : u ≠ v := (SimpleGraph.compl_adj _ _ _).1 hnew |>.1
  have hnnew : ¬(extraBOldGraph data).Adj u v :=
    (SimpleGraph.compl_adj _ _ _).1 hnew |>.2
  have holdRed : (Switching.finalGraph data.cert).Adj u v := by
    by_contra h
    exact hold ((SimpleGraph.compl_adj _ _ _).2 ⟨huv, h⟩)
  by_contra hremoved
  exact hnnew ((extraBOldGraph_adj_iff data u v).2
    (Or.inl ⟨holdRed, hremoved⟩))

end TypeB
end SecondConnector
end RamseyIncrement
