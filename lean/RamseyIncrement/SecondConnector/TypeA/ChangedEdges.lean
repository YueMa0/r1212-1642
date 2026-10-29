/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.TypeA.Construction

/-!
# The additional Type A edge changes

This file audits every edge in (14A).  In particular, it records the
source color in the first-connector graph, the target color in the edited
old graph, and the exact classification of every edge whose color changes.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeA

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private abbrev i0
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.i (i0Index data)

private abbrev a2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c2Index data)

private abbrev y0
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert (some (i0Index data))

private abbrev y2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert (some (i2Index data))

private abbrev yStar
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert none

private abbrev xStar
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

/-! ## Source colors -/

/-- Every edge `cₚx_*`, including all `p ∈ P`, is red before the
additional Type A edit. -/
theorem finalGraph_adj_cp_xStar
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core (data.cert.c p)) (xStar data) := by
  rw [Switching.final_adj_iff]
  left
  constructor
  · rw [Switching.preGraph_adj_lower_x_iff]
    simp [Canonical.secondCertificateAt]
  · rw [Switching.removedRedGraph_adj_iff]
    simp [Switching.SymmPair]

/-- The extra edge `i₀a₂` is blue before the additional Type A edit. -/
theorem finalGraph_not_adj_i0_a2
    (data : Certificates.PlusCaseAData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core (i0 data)) (a2 data) := by
  rw [Switching.final_adj_iff]
  push_neg
  constructor
  · rw [Switching.preGraph_adj_lower_lower_iff,
      specialLift_adj_core_a]
    intro h
    exact (data.cert.c_ne_i (c2Index data) (i0Index data) h).elim
  · rw [Switching.addedRedGraph_adj_iff]
    simp [Switching.SymmPair]

/-- The edge `y₀y_*` is red before the additional Type A edit. -/
theorem finalGraph_adj_y0_yStar
    (data : Certificates.PlusCaseAData G k s) :
    (Switching.finalGraph data.cert).Adj (y0 data) (yStar data) := by
  have hs : 2 < s := by
    have := data.cert.five_le_s
    omega
  have hi01 : i0Index data ≠ Switching.Vertex.i1 data.cert := by
    intro h
    have := congrArg Fin.val h
    simp [i0Index, Switching.Vertex.i1,
      Certificates.i0Index', Certificates.i1Index'] at this
  rw [Switching.final_adj_iff]
  left
  constructor
  · rw [Switching.preGraph_adj_y_y_iff]
    simp [Canonical.outerIndexEquiv, SameBPart]
    omega
  · rw [Switching.removedRedGraph_adj_iff]
    simp [Switching.SymmPair, hi01]

/-- The edge `y₀y₂` is red before the additional Type A edit. -/
theorem finalGraph_adj_y0_y2
    (data : Certificates.PlusCaseAData G k s) :
    (Switching.finalGraph data.cert).Adj (y0 data) (y2 data) := by
  have hi02 : i0Index data ≠ i2Index data := by
    intro h
    have := congrArg Fin.val h
    simp [i0Index, i2Index, Certificates.i0Index',
      Certificates.i2Index'] at this
  have hi01 : i0Index data ≠ Switching.Vertex.i1 data.cert := by
    intro h
    have := congrArg Fin.val h
    simp [i0Index, Switching.Vertex.i1,
      Certificates.i0Index', Certificates.i1Index'] at this
  have hi21 : i2Index data ≠ Switching.Vertex.i1 data.cert := by
    intro h
    have := congrArg Fin.val h
    simp [i2Index, Switching.Vertex.i1,
      Certificates.i2Index', Certificates.i1Index'] at this
  rw [Switching.final_adj_iff]
  left
  constructor
  · rw [Switching.preGraph_adj_y_y_iff]
    simp [Canonical.outerIndexEquiv, SameBPart, hi02]
  · rw [Switching.removedRedGraph_adj_iff]
    simp [Switching.SymmPair, hi01, hi21]

/-- Every explicitly added-red edge has blue source color. -/
theorem extraAAddedRedGraph_source_blue
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraAAddedRedGraph data).Adj u v) :
    ¬(Switching.finalGraph data.cert).Adj u v := by
  rw [extraAAddedRedGraph_adj_iff] at h
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact finalGraph_not_adj_i0_a2 data
  · rcases h with ⟨rfl, rfl⟩
    exact fun huv ↦
      finalGraph_not_adj_i0_a2 data
        ((Switching.finalGraph data.cert).adj_symm huv)

/-- Every explicitly removed-red edge has red source color.  The
quantifier over `p ∈ P` is deliberately retained. -/
theorem extraARemovedRedGraph_source_red
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraARemovedRedGraph data).Adj u v) :
    (Switching.finalGraph data.cert).Adj u v := by
  rw [extraARemovedRedGraph_adj_iff] at h
  rcases h with h | h | h
  · obtain ⟨p, _, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact finalGraph_adj_cp_xStar data p
    · rcases h with ⟨rfl, rfl⟩
      exact (Switching.finalGraph data.cert).adj_symm
        (finalGraph_adj_cp_xStar data p)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact finalGraph_adj_y0_yStar data
    · rcases h with ⟨rfl, rfl⟩
      exact (Switching.finalGraph data.cert).adj_symm
        (finalGraph_adj_y0_yStar data)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact finalGraph_adj_y0_y2 data
    · rcases h with ⟨rfl, rfl⟩
      exact (Switching.finalGraph data.cert).adj_symm
        (finalGraph_adj_y0_y2 data)

/-! ## Non-overlap and target colors -/

/-- The blue-to-red and red-to-blue Type A switch graphs are disjoint. -/
theorem extraAAddedRedGraph_disjoint_extraARemovedRedGraph
    (data : Certificates.PlusCaseAData G k s) :
    Disjoint (extraAAddedRedGraph data)
      (extraARemovedRedGraph data) := by
  rw [SimpleGraph.disjoint_left]
  intro u v hadd hrem
  exact extraAAddedRedGraph_source_blue data hadd
    (extraARemovedRedGraph_source_red data hrem)

/-- Every explicitly added-red edge is red in the edited old graph. -/
theorem extraAOldGraph_adj_of_added
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraAAddedRedGraph data).Adj u v) :
    (extraAOldGraph data).Adj u v := by
  rw [extraAOldGraph_adj_iff]
  exact Or.inr ((extraAAddedRedGraph_adj_iff data u v).1 h)

/-- Every explicitly removed-red edge is blue in the edited old graph. -/
theorem extraAOldGraph_not_adj_of_removed
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : (extraARemovedRedGraph data).Adj u v) :
    ¬(extraAOldGraph data).Adj u v := by
  intro hedge
  rw [extraAOldGraph_adj_iff] at hedge
  rcases hedge with hedge | hedge
  · exact hedge.2 ((extraARemovedRedGraph_adj_iff data u v).1 h)
  · have hadd :
        (extraAAddedRedGraph data).Adj u v :=
      (extraAAddedRedGraph_adj_iff data u v).2 hedge
    exact extraAAddedRedGraph_source_blue data hadd
      (extraARemovedRedGraph_source_red data h)

/-- The added-red switch graph lies in the old blue graph. -/
theorem extraAAddedRedGraph_le_final_compl
    (data : Certificates.PlusCaseAData G k s) :
    extraAAddedRedGraph data ≤
      (Switching.finalGraph data.cert)ᶜ := by
  intro u v h
  exact (SimpleGraph.compl_adj _ _ _).2
    ⟨h.ne, extraAAddedRedGraph_source_blue data h⟩

/-- The removed-red switch graph lies in the old red graph. -/
theorem extraARemovedRedGraph_le_final
    (data : Certificates.PlusCaseAData G k s) :
    extraARemovedRedGraph data ≤
      Switching.finalGraph data.cert := by
  intro u v h
  exact extraARemovedRedGraph_source_red data h

/-! ## Exact changed-edge classification -/

/-- Every red edge present only after the Type A edit is `i₀a₂`. -/
theorem classify_extraA_new_red_edge
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (hnew : (extraAOldGraph data).Adj u v)
    (hold : ¬(Switching.finalGraph data.cert).Adj u v) :
    extraAAddedRedRel data u v := by
  rw [extraAOldGraph_adj_iff] at hnew
  rcases hnew with hnew | hnew
  · exact False.elim (hold hnew.1)
  · exact hnew

/-- Every blue edge present only after the Type A edit is one of the
three declared removed-red families. -/
theorem classify_extraA_new_blue_edge
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (hnew : (extraAOldGraph data)ᶜ.Adj u v)
    (hold : ¬(Switching.finalGraph data.cert)ᶜ.Adj u v) :
    extraARemovedRedRel data u v := by
  have huv : u ≠ v := (SimpleGraph.compl_adj _ _ _).1 hnew |>.1
  have hnnew : ¬(extraAOldGraph data).Adj u v :=
    (SimpleGraph.compl_adj _ _ _).1 hnew |>.2
  have holdRed : (Switching.finalGraph data.cert).Adj u v := by
    by_contra h
    exact hold ((SimpleGraph.compl_adj _ _ _).2 ⟨huv, h⟩)
  by_contra hremoved
  exact hnnew ((extraAOldGraph_adj_iff data u v).2
    (Or.inl ⟨holdRed, hremoved⟩))

end TypeA
end SecondConnector
end RamseyIncrement
