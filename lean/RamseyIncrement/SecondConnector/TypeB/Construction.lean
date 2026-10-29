/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.PlusCertificates
import RamseyIncrement.SecondConnector.Blocks
import RamseyIncrement.SecondConnector.Vertex
import RamseyIncrement.Switching.ChangedEdges

/-!
# The Type B second-connector graph

This file is the declarative implementation of (14B)--(16B).  It edits
`Switching.finalGraph` by the two prescribed switches and then adjoins the
second connector with its prescribed red neighborhood.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

abbrev c2Index (data : Certificates.PlusCaseBData G k s) :
    Fin (k - 1) :=
  Certificates.c2Index data.cert.five_le_k

abbrev i2Index (data : Certificates.PlusCaseBData G k s) :
    Fin (s - 1) :=
  Certificates.i2Index' data.cert.five_le_s

/-- The sole extra Type B edge switched from blue to red: `i₂a₂`. -/
def extraBAddedRedRel
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → Switching.Vertex V k s → Prop :=
  Switching.SymmPair
    (Switching.Vertex.core (data.cert.i (i2Index data)))
    (Switching.Vertex.a (c2Index data))

/-- The sole extra Type B edge switched from red to blue: `c₂x_*`. -/
def extraBRemovedRedRel
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → Switching.Vertex V k s → Prop :=
  Switching.SymmPair
    (Switching.Vertex.core (data.cert.c (c2Index data)))
    (Switching.Vertex.x data.cert none)

/-- The graph consisting of the extra Type B blue-to-red switch. -/
def extraBAddedRedGraph
    (data : Certificates.PlusCaseBData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  SimpleGraph.fromRel (extraBAddedRedRel data)

/-- The graph consisting of the extra Type B red-to-blue switch. -/
def extraBRemovedRedGraph
    (data : Certificates.PlusCaseBData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  SimpleGraph.fromRel (extraBRemovedRedRel data)

private theorem fromRel_adj_iff_of_symmetric_irreflexive
    {α : Type*} (R : α → α → Prop)
    (hsymm : ∀ u v, R u v ↔ R v u)
    (hne : ∀ ⦃u v⦄, R u v → u ≠ v)
    (u v : α) :
    (SimpleGraph.fromRel R).Adj u v ↔ R u v := by
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact (hsymm v u).1 h
  · intro h
    exact ⟨hne h, Or.inl h⟩

private theorem extraBAddedRedRel_ne
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : extraBAddedRedRel data u v) :
    u ≠ v := by
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv

private theorem extraBRemovedRedRel_ne
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (h : extraBRemovedRedRel data u v) :
    u ≠ v := by
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv

@[simp]
theorem extraBAddedRedGraph_adj_iff
    (data : Certificates.PlusCaseBData G k s)
    (u v : Switching.Vertex V k s) :
    (extraBAddedRedGraph data).Adj u v ↔
      extraBAddedRedRel data u v := by
  apply fromRel_adj_iff_of_symmetric_irreflexive
  · intro x y
    exact Switching.symmPair_comm _ _ _ _
  · intro x y h
    exact extraBAddedRedRel_ne data h

@[simp]
theorem extraBRemovedRedGraph_adj_iff
    (data : Certificates.PlusCaseBData G k s)
    (u v : Switching.Vertex V k s) :
    (extraBRemovedRedGraph data).Adj u v ↔
      extraBRemovedRedRel data u v := by
  apply fromRel_adj_iff_of_symmetric_irreflexive
  · intro x y
    exact Switching.symmPair_comm _ _ _ _
  · intro x y h
    exact extraBRemovedRedRel_ne data h

/-- The old Type B graph `H̃_B` from (14B). -/
noncomputable def extraBOldGraph
    (data : Certificates.PlusCaseBData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  (Switching.finalGraph data.cert \ extraBRemovedRedGraph data) ⊔
    extraBAddedRedGraph data

@[simp]
theorem extraBOldGraph_adj_iff
    (data : Certificates.PlusCaseBData G k s)
    (u v : Switching.Vertex V k s) :
    (extraBOldGraph data).Adj u v ↔
      (Switching.finalGraph data.cert).Adj u v ∧
          ¬extraBRemovedRedRel data u v ∨
        extraBAddedRedRel data u v :=
  by
    change
      ((Switching.finalGraph data.cert).Adj u v ∧
          ¬(extraBRemovedRedGraph data).Adj u v) ∨
          (extraBAddedRedGraph data).Adj u v ↔ _
    rw [extraBRemovedRedGraph_adj_iff,
      extraBAddedRedGraph_adj_iff]

/-- The red neighborhood of `w` in (15B)--(16B). -/
def redToWB
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → Prop
  | .inl (.core (.core v)) =>
      (∃ p, v = data.cert.c p) ∨
        G.Adj (data.cert.i (i2Index data)) v
  | .inl (.core (.a p)) => p ≠ c2Index data
  | .inl (.core (.b p)) => 3 ≤ p.val
  | .inl (.a r) =>
      Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r = none
  | .inl (.b r) =>
      let q := Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r
      q = none ∨ q = some (i2Index data)
  | .inr _ => True

@[simp]
theorem redToWB_core
    (data : Certificates.PlusCaseBData G k s) (v : V) :
    redToWB data (Switching.Vertex.core v) ↔
      (∃ p, v = data.cert.c p) ∨
        G.Adj (data.cert.i (i2Index data)) v :=
  Iff.rfl

@[simp]
theorem redToWB_a
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    redToWB data (Switching.Vertex.a p) ↔ p ≠ c2Index data :=
  Iff.rfl

@[simp]
theorem redToWB_b
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    redToWB data (Switching.Vertex.b p) ↔ 3 ≤ p.val :=
  Iff.rfl

@[simp]
theorem redToWB_x
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    redToWB data (Switching.Vertex.x data.cert r) ↔ r = none := by
  simp [redToWB, Switching.Vertex.x]

@[simp]
theorem redToWB_y
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    redToWB data (Switching.Vertex.y data.cert r) ↔
      r = none ∨ r = some (i2Index data) := by
  simp [redToWB, Switching.Vertex.y]

@[simp]
theorem redToWB_z
    (data : Certificates.PlusCaseBData G k s) :
    redToWB data (Switching.Vertex.z : Switching.Vertex V k s) :=
  trivial

/-- The Type B graph after adjoining `w`. -/
noncomputable def plusGraphB
    (data : Certificates.PlusCaseBData G k s) :
    SimpleGraph (SecondConnector.Vertex V k s) :=
  adjoinWithRedNeighborhood (extraBOldGraph data) (redToWB data)

@[simp]
theorem plusGraphB_adj_old_old
    (data : Certificates.PlusCaseBData G k s)
    (u v : Switching.Vertex V k s) :
    (plusGraphB data).Adj (Vertex.old u) (Vertex.old v) ↔
      (extraBOldGraph data).Adj u v :=
  Iff.rfl

@[simp]
theorem plusGraphB_adj_old_w
    (data : Certificates.PlusCaseBData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphB data).Adj (Vertex.old u) Vertex.w ↔ redToWB data u :=
  Iff.rfl

@[simp]
theorem plusGraphB_adj_w_old
    (data : Certificates.PlusCaseBData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphB data).Adj Vertex.w (Vertex.old u) ↔ redToWB data u :=
  Iff.rfl

@[simp]
theorem plusGraphB_not_adj_w_w
    (data : Certificates.PlusCaseBData G k s) :
    ¬(plusGraphB data).Adj (Vertex.w : Vertex V k s) Vertex.w :=
  id

@[simp]
theorem plusGraphB_compl_adj_old_old
    (data : Certificates.PlusCaseBData G k s)
    (u v : Switching.Vertex V k s) :
    (plusGraphB data)ᶜ.Adj (Vertex.old u) (Vertex.old v) ↔
      (extraBOldGraph data)ᶜ.Adj u v := by
  simp [plusGraphB]

@[simp]
theorem plusGraphB_compl_adj_old_w
    (data : Certificates.PlusCaseBData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphB data)ᶜ.Adj (Vertex.old u) Vertex.w ↔ ¬redToWB data u := by
  simp [plusGraphB]

@[simp]
theorem plusGraphB_compl_adj_w_old
    (data : Certificates.PlusCaseBData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphB data)ᶜ.Adj Vertex.w (Vertex.old u) ↔ ¬redToWB data u := by
  simp [plusGraphB]

@[simp]
theorem card_plusGraphB_vertex [Fintype V]
    (data : Certificates.PlusCaseBData G k s) :
    Fintype.card (SecondConnector.Vertex V k s) =
      Fintype.card V + 2 * k + 2 * s :=
  card_plusVertex data.cert

end TypeB
end SecondConnector
end RamseyIncrement
