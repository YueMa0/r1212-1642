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
# The Type A second-connector graph

This file is the declarative implementation of (13A)--(16A).  It edits
`Switching.finalGraph` by one added-red relation and one removed-red
relation, then adjoins the second connector with its prescribed red
neighborhood.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeA

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

abbrev c0Index (data : Certificates.PlusCaseAData G k s) :
    Fin (k - 1) :=
  Certificates.c0Index data.cert.five_le_k

abbrev c1Index (data : Certificates.PlusCaseAData G k s) :
    Fin (k - 1) :=
  Certificates.c1Index data.cert.five_le_k

abbrev c2Index (data : Certificates.PlusCaseAData G k s) :
    Fin (k - 1) :=
  Certificates.c2Index data.cert.five_le_k

abbrev i0Index (data : Certificates.PlusCaseAData G k s) :
    Fin (s - 1) :=
  Certificates.i0Index' data.cert.five_le_s

abbrev i2Index (data : Certificates.PlusCaseAData G k s) :
    Fin (s - 1) :=
  Certificates.i2Index' data.cert.five_le_s

/-- The large row indices `2, ..., k-2`. -/
def largeRows (data : Certificates.PlusCaseAData G k s) :
    Finset (Fin (k - 1)) :=
  Finset.univ.filter fun p ↦ 2 ≤ p.val

/-- `P = β(i₀)` from (13A). -/
noncomputable def P (data : Certificates.PlusCaseAData G k s) :
    Finset (Fin (k - 1)) :=
  data.cert.beta (i0Index data)

/-- `Q = {2, ..., k-2} \ P` from (13A). -/
noncomputable def Q (data : Certificates.PlusCaseAData G k s) :
    Finset (Fin (k - 1)) :=
  largeRows data \ P data

@[simp]
theorem mem_largeRows
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    p ∈ largeRows data ↔ 2 ≤ p.val := by
  simp [largeRows]

@[simp]
theorem mem_P
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    p ∈ P data ↔
      ¬G.Adj (data.cert.c p) (data.cert.i (i0Index data)) := by
  simp [P]

@[simp]
theorem mem_Q
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    p ∈ Q data ↔ 2 ≤ p.val ∧ p ∉ P data := by
  simp [Q]

theorem c0_not_mem_P
    (data : Certificates.PlusCaseAData G k s) :
    c0Index data ∉ P data := by
  intro h
  exact (mem_P data (c0Index data)).1 h data.c0_i0_red

theorem c1_not_mem_P
    (data : Certificates.PlusCaseAData G k s) :
    c1Index data ∉ P data := by
  intro h
  exact (mem_P data (c1Index data)).1 h data.c1_i0_red

theorem c2_mem_P
    (data : Certificates.PlusCaseAData G k s) :
    c2Index data ∈ P data :=
  (mem_P data (c2Index data)).2 data.c2_i0_blue

theorem P_nonempty
    (data : Certificates.PlusCaseAData G k s) :
    (P data).Nonempty :=
  ⟨c2Index data, c2_mem_P data⟩

theorem P_subset_largeRows
    (data : Certificates.PlusCaseAData G k s) :
    P data ⊆ largeRows data := by
  intro p hp
  rw [mem_largeRows]
  have hp0 : p.val ≠ 0 := by
    intro hp0
    have hpc0 : p = c0Index data := by
      apply Fin.ext
      simpa [c0Index, Certificates.c0Index] using hp0
    exact c0_not_mem_P data (hpc0 ▸ hp)
  have hp1 : p.val ≠ 1 := by
    intro hp1
    have hpc1 : p = c1Index data := by
      apply Fin.ext
      simpa [c1Index, Certificates.c1Index] using hp1
    exact c1_not_mem_P data (hpc1 ▸ hp)
  omega

theorem card_largeRows
    (data : Certificates.PlusCaseAData G k s) :
    (largeRows data).card = k - 3 := by
  let e : {p : Fin (k - 1) // p ∈ largeRows data} ≃ Fin (k - 3) :=
  { toFun := fun p ↦
      ⟨p.1.val - 2, by
        have hp := (mem_largeRows data p.1).1 p.2
        have hlt := p.1.isLt
        omega⟩
    invFun := fun q ↦
      ⟨⟨q.val + 2, by
          have hq := q.isLt
          have hk := data.cert.five_le_k
          omega⟩,
        by
          rw [mem_largeRows]
          change 2 ≤ q.val + 2
          omega⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Fin.ext
      have hp := (mem_largeRows data p.1).1 p.2
      simp
      omega
    right_inv := by
      intro q
      apply Fin.ext
      simp }
  calc
    (largeRows data).card =
        Fintype.card {p : Fin (k - 1) // p ∈ largeRows data} :=
      (Fintype.card_coe (largeRows data)).symm
    _ = Fintype.card (Fin (k - 3)) := Fintype.card_congr e
    _ = k - 3 := Fintype.card_fin _

theorem P_disjoint_Q
    (data : Certificates.PlusCaseAData G k s) :
    Disjoint (P data) (Q data) := by
  rw [Finset.disjoint_left]
  intro p hpP hpQ
  exact ((mem_Q data p).1 hpQ).2 hpP

theorem P_union_Q
    (data : Certificates.PlusCaseAData G k s) :
    P data ∪ Q data = largeRows data := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.1 hp with hpP | hpQ
    · exact P_subset_largeRows data hpP
    · exact (mem_largeRows data p).2 ((mem_Q data p).1 hpQ).1
  · intro hp
    by_cases hpP : p ∈ P data
    · exact Finset.mem_union_left _ hpP
    · exact Finset.mem_union_right _
        ((mem_Q data p).2 ⟨(mem_largeRows data p).1 hp, hpP⟩)

theorem card_P_add_card_Q
    (data : Certificates.PlusCaseAData G k s) :
    (P data).card + (Q data).card = k - 3 := by
  have hcard := Finset.card_union_of_disjoint (P_disjoint_Q data)
  rw [P_union_Q, card_largeRows] at hcard
  exact hcard.symm

theorem card_Q_le
    (data : Certificates.PlusCaseAData G k s) :
    (Q data).card ≤ k - 4 := by
  have hP : 1 ≤ (P data).card :=
    Finset.card_pos.mpr (P_nonempty data)
  have hsum := card_P_add_card_Q data
  have hk := data.cert.five_le_k
  omega

/-- The sole extra Type A edge switched from blue to red: `i₀a₂`. -/
def extraAAddedRedRel
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → Switching.Vertex V k s → Prop :=
  Switching.SymmPair
    (Switching.Vertex.core (data.cert.i (i0Index data)))
    (Switching.Vertex.a (c2Index data))

/-- The Type A edges switched from red to blue in (14A). -/
noncomputable def extraARemovedRedRel
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → Switching.Vertex V k s → Prop :=
  fun u v ↦
    (∃ p ∈ P data,
      Switching.SymmPair
        (Switching.Vertex.core (data.cert.c p))
        (Switching.Vertex.x data.cert none) u v) ∨
    Switching.SymmPair
      (Switching.Vertex.y data.cert (some (i0Index data)))
      (Switching.Vertex.y data.cert none) u v ∨
    Switching.SymmPair
      (Switching.Vertex.y data.cert (some (i0Index data)))
      (Switching.Vertex.y data.cert (some (i2Index data))) u v

/-- The graph consisting of the extra Type A blue-to-red switch. -/
def extraAAddedRedGraph
    (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  SimpleGraph.fromRel (extraAAddedRedRel data)

/-- The graph consisting of the extra Type A red-to-blue switches. -/
noncomputable def extraARemovedRedGraph
    (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  SimpleGraph.fromRel (extraARemovedRedRel data)

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

private theorem extraAAddedRedRel_ne
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : extraAAddedRedRel data u v) :
    u ≠ v := by
  rcases h with h | h
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv
  · rcases h with ⟨rfl, rfl⟩
    intro huv
    simpa using congrArg blockTag huv

private theorem extraARemovedRedRel_ne
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (h : extraARemovedRedRel data u v) :
    u ≠ v := by
  rcases h with h | h | h
  · obtain ⟨p, _, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      intro huv
      simpa using congrArg blockTag huv
    · rcases h with ⟨rfl, rfl⟩
      intro huv
      simpa using congrArg blockTag huv
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact (vertex_y_injective data.cert).ne (by simp)
    · rcases h with ⟨rfl, rfl⟩
      exact (vertex_y_injective data.cert).ne (by simp)
  · have hi02 :
        (some (i0Index data) : Option (Fin (s - 1))) ≠
          some (i2Index data) := by
      intro h
      have hindex : i0Index data = i2Index data :=
        Option.some.inj h
      have hval := congrArg Fin.val hindex
      simp [i0Index, i2Index, Certificates.i0Index',
        Certificates.i2Index', Certificates.indexZero] at hval
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact (vertex_y_injective data.cert).ne hi02
    · rcases h with ⟨rfl, rfl⟩
      exact (vertex_y_injective data.cert).ne hi02.symm

@[simp]
theorem extraAAddedRedGraph_adj_iff
    (data : Certificates.PlusCaseAData G k s)
    (u v : Switching.Vertex V k s) :
    (extraAAddedRedGraph data).Adj u v ↔
      extraAAddedRedRel data u v := by
  apply fromRel_adj_iff_of_symmetric_irreflexive
  · intro x y
    exact Switching.symmPair_comm _ _ _ _
  · intro x y h
    exact extraAAddedRedRel_ne data h

@[simp]
theorem extraARemovedRedGraph_adj_iff
    (data : Certificates.PlusCaseAData G k s)
    (u v : Switching.Vertex V k s) :
    (extraARemovedRedGraph data).Adj u v ↔
      extraARemovedRedRel data u v := by
  apply fromRel_adj_iff_of_symmetric_irreflexive
  · intro x y
    simp only [extraARemovedRedRel, Switching.symmPair_comm]
  · intro x y h
    exact extraARemovedRedRel_ne data h

/-- The old Type A graph `H̃_A` from (14A). -/
noncomputable def extraAOldGraph
    (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (Switching.Vertex V k s) :=
  (Switching.finalGraph data.cert \ extraARemovedRedGraph data) ⊔
    extraAAddedRedGraph data

@[simp]
theorem extraAOldGraph_adj_iff
    (data : Certificates.PlusCaseAData G k s)
    (u v : Switching.Vertex V k s) :
    (extraAOldGraph data).Adj u v ↔
      (Switching.finalGraph data.cert).Adj u v ∧
          ¬extraARemovedRedRel data u v ∨
        extraAAddedRedRel data u v :=
  by
    change
      ((Switching.finalGraph data.cert).Adj u v ∧
          ¬(extraARemovedRedGraph data).Adj u v) ∨
          (extraAAddedRedGraph data).Adj u v ↔ _
    rw [extraARemovedRedGraph_adj_iff,
      extraAAddedRedGraph_adj_iff]

/-- The red neighborhood of `w` in (15A)--(16A). -/
noncomputable def redToWA
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → Prop
  | .inl (.core (.core v)) =>
      (∃ p, v = data.cert.c p) ∨
        G.Adj (data.cert.i (i0Index data)) v
  | .inl (.core (.a p)) => p ≠ c2Index data
  | .inl (.core (.b p)) => p ∈ Q data
  | .inl (.a r) =>
      Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r = none
  | .inl (.b r) =>
      let q := Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r
      q = none ∨ q = some (i0Index data) ∨ q = some (i2Index data)
  | .inr _ => True

@[simp]
theorem redToWA_core
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    redToWA data (Switching.Vertex.core v) ↔
      (∃ p, v = data.cert.c p) ∨
        G.Adj (data.cert.i (i0Index data)) v :=
  Iff.rfl

@[simp]
theorem redToWA_a
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    redToWA data (Switching.Vertex.a p) ↔ p ≠ c2Index data :=
  Iff.rfl

@[simp]
theorem redToWA_b
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    redToWA data (Switching.Vertex.b p) ↔ p ∈ Q data :=
  Iff.rfl

@[simp]
theorem redToWA_x
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    redToWA data (Switching.Vertex.x data.cert r) ↔ r = none := by
  simp [redToWA, Switching.Vertex.x]

@[simp]
theorem redToWA_y
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    redToWA data (Switching.Vertex.y data.cert r) ↔
      r = none ∨ r = some (i0Index data) ∨
        r = some (i2Index data) := by
  simp [redToWA, Switching.Vertex.y]

@[simp]
theorem redToWA_z
    (data : Certificates.PlusCaseAData G k s) :
    redToWA data (Switching.Vertex.z : Switching.Vertex V k s) :=
  trivial

/-- The Type A graph after adjoining `w`. -/
noncomputable def plusGraphA
    (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (SecondConnector.Vertex V k s) :=
  adjoinWithRedNeighborhood (extraAOldGraph data) (redToWA data)

@[simp]
theorem plusGraphA_adj_old_old
    (data : Certificates.PlusCaseAData G k s)
    (u v : Switching.Vertex V k s) :
    (plusGraphA data).Adj (Vertex.old u) (Vertex.old v) ↔
      (extraAOldGraph data).Adj u v :=
  Iff.rfl

@[simp]
theorem plusGraphA_adj_old_w
    (data : Certificates.PlusCaseAData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphA data).Adj (Vertex.old u) Vertex.w ↔ redToWA data u :=
  Iff.rfl

@[simp]
theorem plusGraphA_adj_w_old
    (data : Certificates.PlusCaseAData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphA data).Adj Vertex.w (Vertex.old u) ↔ redToWA data u :=
  Iff.rfl

@[simp]
theorem plusGraphA_not_adj_w_w
    (data : Certificates.PlusCaseAData G k s) :
    ¬(plusGraphA data).Adj (Vertex.w : Vertex V k s) Vertex.w :=
  id

@[simp]
theorem plusGraphA_compl_adj_old_old
    (data : Certificates.PlusCaseAData G k s)
    (u v : Switching.Vertex V k s) :
    (plusGraphA data)ᶜ.Adj (Vertex.old u) (Vertex.old v) ↔
      (extraAOldGraph data)ᶜ.Adj u v := by
  simp [plusGraphA]

@[simp]
theorem plusGraphA_compl_adj_old_w
    (data : Certificates.PlusCaseAData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphA data)ᶜ.Adj (Vertex.old u) Vertex.w ↔ ¬redToWA data u := by
  simp [plusGraphA]

@[simp]
theorem plusGraphA_compl_adj_w_old
    (data : Certificates.PlusCaseAData G k s)
    (u : Switching.Vertex V k s) :
    (plusGraphA data)ᶜ.Adj Vertex.w (Vertex.old u) ↔ ¬redToWA data u := by
  simp [plusGraphA]

@[simp]
theorem card_plusGraphA_vertex [Fintype V]
    (data : Certificates.PlusCaseAData G k s) :
    Fintype.card (SecondConnector.Vertex V k s) =
      Fintype.card V + 2 * k + 2 * s :=
  card_plusVertex data.cert

end TypeA
end SecondConnector
end RamseyIncrement
