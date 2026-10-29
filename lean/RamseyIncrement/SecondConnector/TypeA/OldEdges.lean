/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Projection
import RamseyIncrement.SecondConnector.TypeA.ChangedEdges
import RamseyIncrement.Switching.Theorem

/-!
# Safety of the edited Type A old graph

This file formalizes rows (A-R), (A-B1), (A-B2), and (A-B3) of the
strengthened second-connector argument.  The final theorem proves that the
four additional old-old switches preserve `(k+1,s+1)`-freeness.
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

private abbrev i2
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.i (i2Index data)

private abbrev a2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c2Index data)

private abbrev x0
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert (some (i0Index data))

private abbrev x2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert (some (i2Index data))

private abbrev xStar
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

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

/-! ## Stable adjacency equations -/

@[simp]
private theorem old_adj_core_core
    (data : Certificates.PlusCaseAData G k s) (v w : V) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core v) (Switching.Vertex.core w) ↔
      G.Adj v w := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core]
  constructor
  · intro h
    exact h.2 h.1
  · intro h
    exact ⟨h.ne, fun _ ↦ h⟩

@[simp]
private theorem old_adj_a_core
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (v : V) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.a p) (Switching.Vertex.core v) ↔
      data.cert.c p = v ∨
        (p = c2Index data ∧ v = i0 data) := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.core]

@[simp]
private theorem old_adj_core_a
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core v) (Switching.Vertex.a p) ↔
      data.cert.c p = v ∨
        (v = i0 data ∧ p = c2Index data) := by
  rw [(extraAOldGraph data).adj_comm]
  simpa [and_comm] using old_adj_a_core data p v

@[simp]
private theorem old_not_adj_x_x
    (data : Certificates.PlusCaseAData G k s)
    (r t : Option (Fin (s - 1))) :
    ¬(extraAOldGraph data).Adj
      (Switching.Vertex.x data.cert r)
      (Switching.Vertex.x data.cert t) := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.x]

private theorem cert_i_not_red
    (data : Certificates.PlusCaseAData G k s)
    (q r : Fin (s - 1)) :
    ¬G.Adj (data.cert.i q) (data.cert.i r) := by
  by_cases hqr : q = r
  · subst r
    exact G.loopless.irrefl _
  · have hb := data.cert.i_compl_adj hqr
    exact (SimpleGraph.compl_adj _ _ _).1 hb |>.2

private theorem c0_ne_c2
    (data : Certificates.PlusCaseAData G k s) :
    c0Index data ≠ c2Index data := by
  intro h
  have := congrArg Fin.val h
  simp [c0Index, c2Index, Certificates.c0Index,
    Certificates.c2Index] at this

@[simp]
private theorem old_adj_a_a_iff
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.a p) (Switching.Vertex.a q) ↔
      p ≠ q := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a]

@[simp]
private theorem old_adj_i0_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core (i0 data))
        (Switching.Vertex.x data.cert r) ↔
      r ≠ some (i0Index data) := by
  have hiC : ∀ p, i0 data ≠ data.cert.c p :=
    fun p ↦ (data.cert.c_ne_i p (i0Index data)).symm
  cases r with
  | none =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_x_iff,
        Canonical.secondCertificateAt, hiC]
  | some q =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_x_iff,
        Canonical.secondCertificateAt,
        data.cert.i.injective.eq_iff]

@[simp]
private theorem old_adj_a2_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj (a2 data)
      (Switching.Vertex.x data.cert r) ↔ True := by
  constructor
  · intro
    trivial
  · intro
    cases r with
    | none =>
        rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
        simp [extraARemovedRedRel, extraAAddedRedRel,
          Switching.SymmPair, Switching.preGraph_adj_lower_x_iff,
          Canonical.secondCertificateAt, c0_ne_c2 data]
    | some q =>
        rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
        simp [extraARemovedRedRel, extraAAddedRedRel,
          Switching.SymmPair, Switching.preGraph_adj_lower_x_iff,
          Canonical.secondCertificateAt, (c0_ne_c2 data).symm]

@[simp]
private theorem old_adj_i0_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core (i0 data))
        (Switching.Vertex.y data.cert r) ↔
      r = some (i0Index data) := by
  have hiC : ∀ p, i0 data ≠ data.cert.c p :=
    fun p ↦ (data.cert.c_ne_i p (i0Index data)).symm
  cases r with
  | none =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_y_iff,
        Canonical.secondCertificateAt, hiC,
        (hiC (c0Index data)).symm]
  | some q =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_y_iff,
        Canonical.secondCertificateAt,
        data.cert.i.injective.eq_iff, cert_i_not_red data]
      exact eq_comm

@[simp]
private theorem old_adj_a2_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj (a2 data)
        (Switching.Vertex.y data.cert r) ↔
      r = none := by
  cases r with
  | none =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_y_iff,
        Canonical.secondCertificateAt, c0_ne_c2 data]
  | some q =>
      rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
      simp [extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Switching.preGraph_adj_lower_y_iff,
        Canonical.secondCertificateAt, data.cert.c_ne_i,
        (c0_ne_c2 data).symm]

@[simp]
private theorem old_adj_i0_z
    (data : Certificates.PlusCaseAData G k s) :
    (extraAOldGraph data).Adj
      (Switching.Vertex.core (i0 data)) Switching.Vertex.z := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core, Switching.Vertex.b,
    data.c0_i0_red,
    (data.cert.c_ne_i (c0Index data) (i0Index data)).symm]

@[simp]
private theorem old_adj_a2_z
    (data : Certificates.PlusCaseAData G k s) :
    (extraAOldGraph data).Adj (a2 data) Switching.Vertex.z := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b,
    (c0_ne_c2 data).symm]

@[simp]
private theorem old_adj_b_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.b p) (Switching.Vertex.b q) ↔
      (p ≠ q ∧ SameBPart p q) ∨
        Switching.SymmPair (c0Index data) (c2Index data) p q := by
  have h02 := c0_ne_c2 data
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.b]
  constructor <;> aesop

@[simp]
private theorem old_adj_z_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj Switching.Vertex.z
        (Switching.Vertex.x data.cert r) ↔
      r = some (Switching.Vertex.i1 data.cert) ∨ r = none := by
  have hpre :
      (Switching.preGraph data.cert).Adj Switching.Vertex.z
        (Switching.Vertex.x data.cert r) :=
    Switching.preGraph_adj_z_x data.cert r
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, hpre]
  cases r with
  | none => simp
  | some q =>
      by_cases hq : q = Switching.Vertex.i1 data.cert
      · simp [hq]
        intro x hx h
        exact hx h.symm
      · simp [hq, ne_comm]

@[simp]
private theorem old_adj_b0_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.b (c0Index data))
        (Switching.Vertex.x data.cert r) ↔
      r ≠ some (Switching.Vertex.i1 data.cert) ∧ r ≠ none := by
  have hpre :
      (Switching.preGraph data.cert).Adj
        (Switching.Vertex.b (c0Index data))
        (Switching.Vertex.x data.cert r) := by
    rw [Switching.preGraph_adj_lower_x_iff]
    cases r <;> simp [Canonical.secondCertificateAt]
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, hpre, c0_ne_c2 data, ne_comm]

private theorem final_adj_z_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
        Switching.Vertex.z (Switching.Vertex.b p) ↔
      p = c0Index data ∨
        (c0Index data ≠ p ∧ SameBPart (c0Index data) p) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.canonicalGraph, Canonical.graph,
    Switching.Vertex.b]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, (h.2 h.1).2⟩
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, fun hn ↦ ⟨hn, h.2⟩⟩

@[simp]
private theorem old_adj_z_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        Switching.Vertex.z (Switching.Vertex.b p) ↔
      p = c0Index data ∨
        (c0Index data ≠ p ∧ SameBPart (c0Index data) p) := by
  rw [extraAOldGraph_adj_iff, final_adj_z_b_iff]
  simp [extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair]

/-! ## Row (A-R) -/

/-- Exact block classifier for the red common neighborhood in (17A). -/
private theorem mem_common_ar_iff
    (data : Certificates.PlusCaseAData G k s)
    (w : Switching.Vertex V k s) :
    w ∈ (extraAOldGraph data).commonNeighbors
        (Switching.Vertex.core (i0 data)) (a2 data) ↔
      (∃ p, p ∉ P data ∧ w = Switching.Vertex.b p) ∨
      (∃ r, r ≠ some (i0Index data) ∧
        w = Switching.Vertex.x data.cert r) ∨
      w = Switching.Vertex.z := by
  rw [SimpleGraph.mem_commonNeighbors]
  rcases vertex_six_block_cases data.cert w with
      ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ |
      ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
  · rw [old_adj_core_core, old_adj_a_core]
    constructor
    · rintro ⟨hiv, hcv | hadded⟩
      · subst v
        exact (data.c2_i0_blue (G.adj_symm hiv)).elim
      · rcases hadded with ⟨_, rfl⟩
        exact (G.loopless.irrefl _ hiv).elim
    · simp
  · rw [old_adj_core_a, old_adj_a_a_iff]
    simp [data.cert.c_ne_i]
    intro h
    exact h.symm
  · simp [extraAOldGraph_adj_iff, extraARemovedRedRel,
      extraAAddedRedRel, Switching.SymmPair,
      Switching.finalGraph, Switching.preGraph,
      Switching.canonicalGraph, Canonical.graph,
      Switching.removedRedGraph, Switching.removedRedRel,
      Switching.addedRedGraph, Switching.addedRedRel,
      Switching.Vertex.core, Switching.Vertex.a,
      Switching.Vertex.b, mem_P, SameBPart,
      data.cert.c_ne_i]
    constructor
    · rintro ⟨⟨_, hpRed⟩, hp2⟩
      exact hpRed
    · intro hpRed
      refine ⟨⟨(data.cert.c_ne_i p (i0Index data)).symm,
        hpRed⟩, ?_⟩
      intro hp2
      subst p
      exact data.c2_i0_blue hpRed
  · rw [old_adj_i0_x_iff, old_adj_a2_x_iff]
    simp
  · rw [old_adj_i0_y_iff, old_adj_a2_y_iff]
    simp
    intro hr hnone
    rw [hr] at hnone
    simp at hnone
  · simp only [old_adj_i0_z, old_adj_a2_z]
    simp

private theorem b_not_mem_P_of_mem_common_ar
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1))
    (hp : Switching.Vertex.b p ∈
      (extraAOldGraph data).commonNeighbors
        (Switching.Vertex.core (i0 data)) (a2 data)) :
    p ∉ P data := by
  rcases (mem_common_ar_iff data _).1 hp with h | h | h
  · obtain ⟨q, hq, heq⟩ := h
    have hpq : p = q := vertex_b_injective heq
    simpa [hpq] using hq
  · obtain ⟨r, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem card_bIn_le_sub_three
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hpair : ∀ p q : BIn K, p ≠ q →
      SameBPart p.1 q.1) :
    Fintype.card (BIn K) ≤ k - 3 := by
  classical
  by_cases hempty : IsEmpty (BIn K)
  · have : Fintype.card (BIn K) = 0 := Fintype.card_eq_zero
    omega
  · letI : Nonempty (BIn K) := not_isEmpty_iff.mp hempty
    let q₀ : BIn K := Classical.choice inferInstance
    by_cases hsmall : q₀.1.1 < 2
    · have hall : ∀ q : BIn K, q.1.1 < 2 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using hsmall
        · rcases hpair q q₀ hq with h | h
          · exact h.1
          · omega
      let f : BIn K ↪ Fin 2 :=
        { toFun := fun q ↦ ⟨q.1.1, hall q⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin 2 ↦ x.val) hpq }
      have hcard : Fintype.card (BIn K) ≤ 2 := by
        simpa using Fintype.card_le_of_injective f f.injective
      have hk := data.cert.five_le_k
      omega
    · have hall : ∀ q : BIn K, 2 ≤ q.1.1 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using Nat.le_of_not_gt hsmall
        · rcases hpair q q₀ hq with h | h
          · omega
          · exact h.1
      let f : BIn K ↪ Fin (k - 3) :=
        { toFun := fun q ↦
            ⟨q.1.1 - 2, by
              have hlt := q.1.2
              omega⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            have hv := congrArg Fin.val hpq
            dsimp at hv
            have hp := hall p
            have hq := hall q
            omega }
      simpa using Fintype.card_le_of_injective f f.injective

/-- Row A-R: deleting the endpoints `i₀,a₂` leaves no red
`K_(k-1)` in their common neighborhood. -/
theorem red_common_i0_a2_cliqueFree
    (data : Certificates.PlusCaseAData G k s) :
    (extraAOldGraph data).CliqueFreeOn
      ((extraAOldGraph data).commonNeighbors
        (Switching.Vertex.core (i0 data)) (a2 data))
      (k - 1) := by
  classical
  intro K hKsub hK
  have hCoreZero : Fintype.card (CoreIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases (mem_common_ar_iff data _).1 (hKsub d.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro a
    rcases (mem_common_ar_iff data _).1 (hKsub a.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hYZero : Fintype.card (YIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro y
    rcases (mem_common_ar_iff data _).1 (hKsub y.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hBpair :
      ∀ p q : BIn K, p ≠ q → SameBPart p.1 q.1 := by
    intro p q hpq
    have hpP := b_not_mem_P_of_mem_common_ar data p.1 (hKsub p.2)
    have hqP := b_not_mem_P_of_mem_common_ar data q.1 (hKsub q.2)
    have hpqv :
        (Switching.Vertex.b p.1 : Switching.Vertex V k s) ≠
          Switching.Vertex.b q.1 := by
      intro h
      apply hpq
      apply Subtype.ext
      exact vertex_b_injective h
    rcases (old_adj_b_b_iff data p.1 q.1).1
        (hK.isClique p.2 q.2 hpqv) with hsame | hspecial
    · exact hsame.2
    · rcases hspecial with hspecial | hspecial
      · exact False.elim (hqP (hspecial.2 ▸ c2_mem_P data))
      · exact False.elim (hpP (hspecial.1 ▸ c2_mem_P data))
  have hBle : Fintype.card (BIn K) ≤ k - 3 :=
    card_bIn_le_sub_three data hBpair
  have hXle : Fintype.card (XIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    by_contra hrt
    have hrtv :
        Switching.Vertex.x data.cert r.1 ≠
          Switching.Vertex.x data.cert t.1 := by
      intro h
      apply hrt
      apply Subtype.ext
      exact (vertex_x_injective data.cert) h
    exact old_not_adj_x_x data r.1 t.1
      (hK.isClique r.2 t.2 hrtv)
  have hZle : Fintype.card (ZIn K) ≤ 1 :=
    card_zIn_le_one K
  have hparts := card_eq_six_blocks data.cert K
  have hcard := hK.card_eq
  by_cases hz : (Switching.Vertex.z : Switching.Vertex V k s) ∈ K
  · have hBsmall : ∀ p : BIn K, p.1.val < 2 := by
      intro p
      have hzp :
          (extraAOldGraph data).Adj Switching.Vertex.z
            (Switching.Vertex.b p.1) :=
        hK.isClique hz p.2 (by simp)
      rcases (old_adj_z_b_iff data p.1).1 hzp with hp0 | hp
      · have hpval := congrArg Fin.val hp0
        simp [c0Index, Certificates.c0Index] at hpval
        omega
      · rcases hp.2 with hpSmall | hpLarge
        · exact hpSmall.2
        · have h0 : ¬2 ≤ (c0Index data).val := by
            simp [c0Index, Certificates.c0Index]
          exact False.elim (h0 hpLarge.1)
    have hBtwo : Fintype.card (BIn K) ≤ 2 := by
      let f : BIn K ↪ Fin 2 :=
        { toFun := fun p ↦ ⟨p.1.val, hBsmall p⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin 2 ↦ x.val) hpq }
      simpa using Fintype.card_le_of_injective f f.injective
    by_cases hXempty : IsEmpty (XIn data.cert K)
    · have hXzero : Fintype.card (XIn data.cert K) = 0 :=
        Fintype.card_eq_zero
      have hk := data.cert.five_le_k
      omega
    · letI : Nonempty (XIn data.cert K) :=
        not_isEmpty_iff.mp hXempty
      let r₀ : XIn data.cert K := Classical.choice inferInstance
      have hrCases :
          r₀.1 = some (Switching.Vertex.i1 data.cert) ∨
            r₀.1 = none := by
        have hzr :
            (extraAOldGraph data).Adj Switching.Vertex.z
              (Switching.Vertex.x data.cert r₀.1) :=
          hK.isClique hz r₀.2 (by simp)
        exact (old_adj_z_x_iff data r₀.1).1 hzr
      have hBnot0 : ∀ p : BIn K, p.1 ≠ c0Index data := by
        intro p hp0
        have hpr :
            (extraAOldGraph data).Adj
              (Switching.Vertex.b (c0Index data))
              (Switching.Vertex.x data.cert r₀.1) := by
          rw [← hp0]
          exact hK.isClique p.2 r₀.2 (by simp)
        have hboth := (old_adj_b0_x_iff data r₀.1).1 hpr
        rcases hrCases with hr | hr
        · exact hboth.1 hr
        · exact hboth.2 hr
      have hBone : Fintype.card (BIn K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro p q
        apply Subtype.ext
        apply Fin.ext
        have hpSmall := hBsmall p
        have hqSmall := hBsmall q
        have hp0 := hBnot0 p
        have hq0 := hBnot0 q
        have hpval : p.1.val = 1 := by
          have : p.1.val ≠ 0 := by
            intro hp
            apply hp0
            apply Fin.ext
            simpa [c0Index, Certificates.c0Index] using hp
          omega
        have hqval : q.1.val = 1 := by
          have : q.1.val ≠ 0 := by
            intro hq
            apply hq0
            apply Fin.ext
            simpa [c0Index, Certificates.c0Index] using hq
          omega
        omega
      have hk := data.cert.five_le_k
      omega
  · have hZzero : Fintype.card (ZIn K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro z
      exact hz (by simpa using z.2)
    have hk := data.cert.five_le_k
    omega

/-! ## Row (A-B1) -/

private theorem final_adj_core_xStar
    (data : Certificates.PlusCaseAData G k s)
    (v : V) :
    (Switching.finalGraph data.cert).Adj
        (Switching.Vertex.core v) (xStar data) := by
  rw [Switching.final_adj_iff]
  left
  constructor
  · rw [Switching.preGraph_adj_lower_x_iff]
    simp [Canonical.secondCertificateAt]
  · rw [Switching.removedRedGraph_adj_iff]
    simp [Switching.SymmPair]

@[simp]
private theorem old_adj_a_xStar_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.a q) (xStar data) ↔
      q ≠ c0Index data := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]
  exact ne_comm

private theorem old_adj_b_xStar_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.b q) (xStar data) ↔
      q ≠ c0Index data := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]

@[simp]
private theorem old_adj_cp_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core (data.cert.c p))
        (Switching.Vertex.x data.cert r) ↔
      r ≠ none := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  cases r with
  | none =>
      simp [Switching.preGraph_adj_lower_x_iff,
        Switching.removedRedGraph_adj_iff,
        Switching.addedRedGraph_adj_iff,
        extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Canonical.secondCertificateAt, hp]
      exact (mem_P data p).1 hp
  | some q =>
      simp [Switching.preGraph_adj_lower_x_iff,
        Switching.removedRedGraph_adj_iff,
        Switching.addedRedGraph_adj_iff,
        extraARemovedRedRel, extraAAddedRedRel,
        Switching.SymmPair, Canonical.secondCertificateAt,
        data.cert.c_ne_i]
      exact (data.cert.c_ne_i p q).symm

@[simp]
private theorem old_adj_xStar_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj (xStar data)
        (Switching.Vertex.y data.cert r) ↔
      r = none := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.outerIndexEquiv]
  exact eq_comm

@[simp]
private theorem old_adj_cp_y_some_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core (data.cert.c p))
        (Switching.Vertex.y data.cert (some q)) ↔
      G.Adj (data.cert.c p) (data.cert.i q) := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    data.cert.c_ne_i, ne_comm]
  exact G.adj_comm _ _

@[simp]
private theorem old_adj_cp_yStar_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data) :
    ¬(extraAOldGraph data).Adj
        (Switching.Vertex.core (data.cert.c p)) (yStar data) := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]
  intro h
  subst p
  exact c0_not_mem_P data hp

/-- Structural form of (18A). -/
private theorem common_ab1_cases
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data)
    {w : Switching.Vertex V k s}
    (hw : w ∈ (extraAOldGraph data)ᶜ.commonNeighbors
        (Switching.Vertex.core (data.cert.c p)) (xStar data)) :
    w = Switching.Vertex.a (c0Index data) ∨
      ∃ q : Fin (s - 1),
        ¬G.Adj (data.cert.c p) (data.cert.i q) ∧
          w = Switching.Vertex.y data.cert (some q) := by
  obtain ⟨hcp, hxs⟩ :=
    (extraAOldGraph data)ᶜ.mem_commonNeighbors.1 hw
  rcases vertex_six_block_cases data.cert w with
      ⟨v, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ |
      ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
  · have hnotx := (SimpleGraph.compl_adj _ _ _).1 hxs |>.2
    have hremoved : extraARemovedRedRel data
        (xStar data) (Switching.Vertex.core v) := by
      by_contra hrem
      exact hnotx ((extraAOldGraph_adj_iff data _ _).2
        (Or.inl ⟨(Switching.finalGraph data.cert).adj_symm
          (final_adj_core_xStar data v), hrem⟩))
    rcases hremoved with hremoved | hremoved | hremoved
    · obtain ⟨q, hqP, hpair⟩ := hremoved
      rcases hpair with hpair | hpair
      · have := congrArg blockTag hpair.1
        simp at this
      · have hv : v = data.cert.c q :=
          vertex_core_injective hpair.2
        have hnotcp := (SimpleGraph.compl_adj _ _ _).1 hcp |>.2
        rw [old_adj_core_core] at hnotcp
        subst v
        by_cases hpq : p = q
        · subst q
          exact False.elim
            (((SimpleGraph.compl_adj _ _ _).1 hcp).1 rfl)
        · exact False.elim (hnotcp (data.cert.c_adj hpq))
    · rcases hremoved with hremoved | hremoved
      · have := congrArg blockTag hremoved.1
        simp at this
      · have := congrArg blockTag hremoved.1
        simp at this
    · rcases hremoved with hremoved | hremoved
      · have := congrArg blockTag hremoved.1
        simp at this
      · have := congrArg blockTag hremoved.1
        simp at this
  · have hnot := (SimpleGraph.compl_adj _ _ _).1 hxs |>.2
    have hq0 : q = c0Index data := by
      by_contra hq
      exact hnot ((extraAOldGraph data).adj_symm
        ((old_adj_a_xStar_iff data q).2 hq))
    exact Or.inl (congrArg Switching.Vertex.a hq0)
  · by_cases hq0 : q = c0Index data
    · subst q
      have hpc0 :
          (extraAOldGraph data).Adj
            (Switching.Vertex.core (data.cert.c p))
            (Switching.Vertex.b (c0Index data)) := by
        rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
        simp [Switching.preGraph_adj_lower_lower_iff,
          Switching.removedRedGraph_adj_iff,
          Switching.addedRedGraph_adj_iff,
          extraARemovedRedRel, extraAAddedRedRel,
          Switching.SymmPair, specialLift_adj_core_b,
          data.cert.c_adj]
        have hp0 : p ≠ c0Index data := by
          intro h
          subst p
          exact c0_not_mem_P data hp
        exact ⟨hp0, data.cert.c_adj hp0.symm⟩
      exact False.elim
        ((SimpleGraph.compl_adj _ _ _).1 hcp |>.2 hpc0)
    · exact False.elim
        ((SimpleGraph.compl_adj _ _ _).1 hxs |>.2
          ((extraAOldGraph data).adj_symm
            ((old_adj_b_xStar_iff data q).2 hq0)))
  · cases r with
    | none =>
        exact False.elim
          (((SimpleGraph.compl_adj _ _ _).1 hxs).1 rfl)
    | some q =>
        exact False.elim
          ((SimpleGraph.compl_adj _ _ _).1 hcp |>.2
            ((old_adj_cp_x_iff data p hp (some q)).2 (by simp)))
  · cases r with
    | none =>
        exact False.elim
          ((SimpleGraph.compl_adj _ _ _).1 hxs |>.2
            ((old_adj_xStar_y_iff data none).2 rfl))
    | some q =>
        refine Or.inr ⟨q, ?_, rfl⟩
        intro hred
        exact (SimpleGraph.compl_adj _ _ _).1 hcp |>.2
          ((old_adj_cp_y_some_iff data p q).2 hred)
  · exact False.elim
      ((SimpleGraph.compl_adj _ _ _).1 hxs |>.2
        ((extraAOldGraph data).adj_symm
          ((old_adj_z_x_iff data none).2 (Or.inr rfl))))

@[simp]
private theorem blue_adj_y0_ySome_iff
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (q : Fin (s - 1)) :
    (extraAOldGraph data)ᶜ.Adj (y0 data)
        (Switching.Vertex.y data.cert (some q)) ↔
      q = Switching.Vertex.i1 data.cert ∨ q = i2Index data := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  simp [SimpleGraph.compl_adj, extraAOldGraph,
    extraARemovedRedGraph, extraARemovedRedRel,
    extraAAddedRedGraph, extraAAddedRedRel,
    Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.SymmPair, Switching.Vertex.y,
    Switching.Vertex.i1, SameBPart, hE,
    i0Index, i2Index, Certificates.i0Index',
    Certificates.i1Index', Certificates.i2Index']
  simp [Certificates.indexZero, Certificates.indexOne, Fin.ext_iff]
  omega

private theorem old_adj_y1_y2
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.y data.cert
          (some (Switching.Vertex.i1 data.cert))) (y2 data) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [extraAOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · rw [Switching.preGraph_adj_y_y_iff]
      simp [Canonical.outerIndexEquiv, SameBPart,
        Switching.Vertex.i1, i2Index,
        Certificates.i1Index', Certificates.i2Index',
        Certificates.indexOne]
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair, hE, Switching.Vertex.i1,
        i0Index, i2Index, Certificates.i0Index',
        Certificates.i1Index', Certificates.i2Index',
        Certificates.indexZero, Certificates.indexOne, Fin.ext_iff]
  · simp [extraARemovedRedRel, extraAAddedRedRel,
      Switching.SymmPair, Switching.Vertex.i1,
      i0Index, i2Index, Certificates.i0Index',
      Certificates.i1Index', Certificates.i2Index',
      Certificates.indexZero, Certificates.indexOne, Fin.ext_iff]

private theorem yIn_ab1_some
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors
        (Switching.Vertex.core (data.cert.c p)) (xStar data))
    (r : YIn data.cert K) :
    ∃ q : Fin (s - 1), r.1 = some q := by
  rcases common_ab1_cases data p hp (hKsub r.2) with h | h
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨q, _, heq⟩ := h
    exact ⟨q, vertex_y_injective data.cert heq⟩

private theorem card_yIn_ab1_le_two_of_y0
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors
        (Switching.Vertex.core (data.cert.c p)) (xStar data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hy0 : y0 data ∈ K) :
    Fintype.card (YIn data.cert K) ≤ 2 := by
  classical
  let rzero : YIn data.cert K :=
    ⟨some (i0Index data), hy0⟩
  by_cases hall : ∀ r : YIn data.cert K, r = rzero
  · have hle : Fintype.card (YIn data.cert K) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      exact fun r t ↦ (hall r).trans (hall t).symm
    omega
  · push Not at hall
    obtain ⟨r₀, hr₀⟩ := hall
    have hcollapse :
        ∀ r : YIn data.cert K, r = rzero ∨ r = r₀ := by
      intro r
      by_cases hrz : r = rzero
      · exact Or.inl hrz
      · right
        obtain ⟨q, hq⟩ := yIn_ab1_some data p hp hKsub r
        obtain ⟨t, ht⟩ := yIn_ab1_some data p hp hKsub r₀
        have hq0 : q ≠ i0Index data := by
          intro h
          apply hrz
          apply Subtype.ext
          exact hq.trans (congrArg some h)
        have ht0 : t ≠ i0Index data := by
          intro h
          apply hr₀
          apply Subtype.ext
          exact ht.trans (congrArg some h)
        have hy0r :
            (extraAOldGraph data)ᶜ.Adj (y0 data)
              (Switching.Vertex.y data.cert (some q)) := by
          rw [← hq]
          exact hK hy0 r.2 (by
            intro h
            apply hrz
            apply Subtype.ext
            exact (vertex_y_injective data.cert) h.symm)
        have hy0t :
            (extraAOldGraph data)ᶜ.Adj (y0 data)
              (Switching.Vertex.y data.cert (some t)) := by
          rw [← ht]
          exact hK hy0 r₀.2 (by
            intro h
            apply hr₀
            apply Subtype.ext
            exact (vertex_y_injective data.cert) h.symm)
        have hqCases := (blue_adj_y0_ySome_iff data hG q).1 hy0r
        have htCases := (blue_adj_y0_ySome_iff data hG t).1 hy0t
        have hqt : q = t := by
          by_cases hrr : r = r₀
          · subst r₀
            exact Option.some.inj (hq.symm.trans ht)
          have hblue :
              (extraAOldGraph data)ᶜ.Adj
                (Switching.Vertex.y data.cert (some q))
                (Switching.Vertex.y data.cert (some t)) := by
            rw [← hq, ← ht]
            exact hK r.2 r₀.2 (by
              intro h
              apply hrr
              apply Subtype.ext
              exact (vertex_y_injective data.cert) h)
          rcases hqCases with hq1 | hq2 <;>
            rcases htCases with ht1 | ht2
          · exact hq1.trans ht1.symm
          · exfalso
            exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              (hq1 ▸ ht2 ▸ old_adj_y1_y2 data hG)
          · exfalso
            exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              ((extraAOldGraph data).adj_symm
                (ht1 ▸ hq2 ▸ old_adj_y1_y2 data hG))
          · exact hq2.trans ht2.symm
        apply Subtype.ext
        exact hq.trans ((congrArg some hqt).trans ht.symm)
    let f : YIn data.cert K ↪ Fin 2 :=
      { toFun := fun r ↦ if r = rzero then 0 else 1
        inj' := by
          intro r t hrt
          by_cases hrz : r = rzero
          · have htz : t = rzero := by
              by_contra htn
              simp [hrz, htn] at hrt
            exact hrz.trans htz.symm
          · have htn : t ≠ rzero := by
              intro htz
              simp [hrz, htz] at hrt
            exact (hcollapse r).resolve_left hrz |>.trans
              ((hcollapse t).resolve_left htn).symm }
    simpa using Fintype.card_le_of_injective f f.injective

/-- Row A-B1: every newly blue `cₚx_*`, `p ∈ P`, has a common
blue neighborhood with no `K_(s-1)`. -/
theorem blue_common_cp_xStar_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data) :
    (extraAOldGraph data)ᶜ.CliqueFreeOn
      ((extraAOldGraph data)ᶜ.commonNeighbors
        (Switching.Vertex.core (data.cert.c p)) (xStar data))
      (s - 1) := by
  classical
  intro K hKsub hK
  have hCoreZero : Fintype.card (CoreIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab1_cases data p hp (hKsub d.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, h⟩ := h
      have := congrArg blockTag h
      simp at this
  have hBZero : Fintype.card (BIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab1_cases data p hp (hKsub d.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, h⟩ := h
      have := congrArg blockTag h
      simp at this
  have hXZero : Fintype.card (XIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab1_cases data p hp (hKsub d.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, h⟩ := h
      have := congrArg blockTag h
      simp at this
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab1_cases data p hp (hKsub d.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, h⟩ := h
      have := congrArg blockTag h
      simp at this
  have haIndex : ∀ a : AIn K, a.1 = c0Index data := by
    intro a
    rcases common_ab1_cases data p hp (hKsub a.2) with h | h
    · exact vertex_a_injective h
    · obtain ⟨q, _, h⟩ := h
      have := congrArg blockTag h
      simp at this
  have hAle : Fintype.card (AIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro a b
    apply Subtype.ext
    exact (haIndex a).trans (haIndex b).symm
  have hparts := card_eq_six_blocks data.cert K
  have hcard := hK.card_eq
  by_cases hy0 : y0 data ∈ K
  · have hYle :=
      card_yIn_ab1_le_two_of_y0 data hG p hp hKsub hK.isClique hy0
    have hs := data.cert.five_le_s
    omega
  · let qOf : YIn data.cert K → Fin (s - 1) :=
      fun r ↦ Classical.choose (yIn_ab1_some data p hp hKsub r)
    have qOf_spec (r : YIn data.cert K) :
        r.1 = some (qOf r) :=
      Classical.choose_spec (yIn_ab1_some data p hp hKsub r)
    have qOf_inj : Function.Injective qOf := by
      intro r t hrt
      apply Subtype.ext
      rw [qOf_spec r, qOf_spec t, hrt]
    have qOf_ne_i0 (r : YIn data.cert K) :
        qOf r ≠ i0Index data := by
      intro hr
      apply hy0
      have hrmem := r.2
      simpa [qOf_spec r, hr] using hrmem
    have cp_blue_q (r : YIn data.cert K) :
        ¬G.Adj (data.cert.c p) (data.cert.i (qOf r)) := by
      rcases common_ab1_cases data p hp (hKsub r.2) with h | h
      · have := congrArg blockTag h
        simp at this
      · obtain ⟨q, hblue, heq⟩ := h
        have hrq : r.1 = some q :=
          vertex_y_injective data.cert heq
        have : q = qOf r :=
          Option.some.inj (hrq.symm.trans (qOf_spec r))
        simpa [← this] using hblue
    let f : (YIn data.cert K ⊕ Bool) ↪ V :=
      { toFun
          | Sum.inl r => data.cert.i (qOf r)
          | Sum.inr false => data.cert.c p
          | Sum.inr true => data.cert.i (i0Index data)
        inj' := by
          intro x y hxy
          rcases x with r | b <;> rcases y with t | c
          · exact congrArg Sum.inl
              (qOf_inj (data.cert.i.injective hxy))
          · cases c with
            | false =>
                exact False.elim
                  ((data.cert.c_ne_i p (qOf r)).symm hxy)
            | true =>
                exact False.elim
                  (qOf_ne_i0 r (data.cert.i.injective hxy))
          · cases b with
            | false =>
                exact False.elim (data.cert.c_ne_i p (qOf t) hxy)
            | true =>
                exact False.elim
                  (qOf_ne_i0 t (data.cert.i.injective hxy.symm))
          · cases b <;> cases c
            · rfl
            · exact False.elim
                (data.cert.c_ne_i p (i0Index data) hxy)
            · exact False.elim
                ((data.cert.c_ne_i p (i0Index data)).symm hxy)
            · rfl }
    have hproj :
        Fintype.card (YIn data.cert K ⊕ Bool) < s := by
      apply card_lt_of_cliqueFreeOn_of_embedding
        hG.2.cliqueFreeOn f
      · intro
        exact Set.mem_univ _
      · intro x y hxy
        rcases x with r | b <;> rcases y with t | c
        · exact data.cert.i_compl_adj
            (fun h ↦ hxy (congrArg Sum.inl (qOf_inj h)))
        · cases c with
          | false =>
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨(data.cert.c_ne_i p (qOf r)).symm,
                  fun h ↦ cp_blue_q r (G.adj_symm h)⟩
          | true =>
              exact data.cert.i_compl_adj (qOf_ne_i0 r)
        · cases b with
          | false =>
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨data.cert.c_ne_i p (qOf t), cp_blue_q t⟩
          | true =>
              exact data.cert.i_compl_adj (qOf_ne_i0 t).symm
        · cases b <;> cases c
          · exact False.elim (hxy rfl)
          · exact (SimpleGraph.compl_adj _ _ _).2
              ⟨data.cert.c_ne_i p (i0Index data),
                (mem_P data p).1 hp⟩
          · exact (SimpleGraph.compl_adj _ _ _).2
              ⟨(data.cert.c_ne_i p (i0Index data)).symm,
                fun h ↦ (mem_P data p).1 hp (G.adj_symm h)⟩
          · exact False.elim (hxy rfl)
    simp at hproj
    omega

/-! ## Row (A-B2) -/

@[simp]
private theorem old_adj_y0_core_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) :
    (extraAOldGraph data).Adj (y0 data)
        (Switching.Vertex.core v) ↔
      v = i0 data ∨ G.Adj (i0 data) v := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    data.cert.c_ne_i, ne_comm]

@[simp]
private theorem old_adj_yStar_core_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) :
    (extraAOldGraph data).Adj (yStar data)
        (Switching.Vertex.core v) ↔
      v = data.cert.c (c0Index data) := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]
  exact eq_comm

private theorem old_adj_yStar_a
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj (yStar data)
        (Switching.Vertex.a p) := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    old_adj_a_a_iff]
  by_cases hp : p = c0Index data
  · exact Or.inl hp
  · exact Or.inr (fun h ↦ hp h.symm)

private theorem old_adj_yStar_b
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj (yStar data)
        (Switching.Vertex.b p) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    by_cases hp : p = c0Index data
    · right
      rw [Switching.addedRedGraph_adj_iff]
      simp [Switching.SymmPair, hp]
    · left
      constructor
      · rw [Switching.preGraph_adj_lower_y_iff]
        simp [Canonical.secondCertificateAt,
          specialLift_adj_b_a, hp]
        exact fun h ↦ hp h.symm
      · rw [Switching.removedRedGraph_adj_iff]
        simp [Switching.SymmPair, hE]
  · simp [extraARemovedRedRel, Switching.SymmPair]

@[simp]
private theorem old_adj_y0_x_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj (y0 data)
        (Switching.Vertex.x data.cert r) ↔
      r = some (i0Index data) := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.outerIndexEquiv]

@[simp]
private theorem old_adj_x_yStar_iff
    (data : Certificates.PlusCaseAData G k s)
    (r : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.x data.cert r) (yStar data) ↔
      r = none := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.outerIndexEquiv]

private theorem old_adj_y1_yStar
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data).Adj
      (Switching.Vertex.y data.cert
        (some (Switching.Vertex.i1 data.cert))) (yStar data) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [extraAOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · exact Switching.preGraph_adj_y1_yStar data.cert
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair, hE]
  · simp [extraARemovedRedRel, Switching.SymmPair,
      Switching.Vertex.i1, i0Index, i2Index,
      Certificates.i0Index', Certificates.i1Index',
      Certificates.i2Index', Certificates.indexZero,
      Certificates.indexOne, Fin.ext_iff]

private theorem old_adj_y0_z
    (data : Certificates.PlusCaseAData G k s) :
    (extraAOldGraph data).Adj (y0 data)
      Switching.Vertex.z := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · have hb :
          (Switching.preGraph data.cert).Adj
            (Switching.Vertex.b (c0Index data)) (y0 data) := by
          rw [Switching.preGraph_adj_lower_y_iff]
          simp [Canonical.secondCertificateAt,
            specialLift_adj_b_core, data.c0_i0_red,
            data.cert.c_ne_i]
          exact (data.cert.c_ne_i
            (c0Index data) (i0Index data)).symm
      change (Switching.redJoinedClone
          (Switching.canonicalGraph data.cert)
          (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
            Switching.CloneVertex.z
            (.inl (.b ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                data.cert.five_le_s)).symm
                  (some (i0Index data)))))
      rw [Switching.redJoinedClone.adj_z_old]
      right
      simpa [Switching.preGraph] using hb
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair, Switching.Vertex.y,
        Switching.Vertex.x]
  · simp [extraARemovedRedRel, Switching.SymmPair,
      Switching.Vertex.y, Switching.Vertex.x]

private theorem common_ab2_cases
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {w : Switching.Vertex V k s}
    (hw : w ∈ (extraAOldGraph data)ᶜ.commonNeighbors
      (y0 data) (yStar data)) :
    (∃ v : V, ¬G.Adj (i0 data) v ∧
      w = Switching.Vertex.core v) ∨
    (∃ r : Option (Fin (s - 1)),
      r ≠ some (i0Index data) ∧ r ≠ none ∧
        w = Switching.Vertex.x data.cert r) ∨
      w = y2 data := by
  obtain ⟨hy0w, hysw⟩ :=
    (extraAOldGraph data)ᶜ.mem_commonNeighbors.1 hw
  rcases vertex_six_block_cases data.cert w with
      ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ |
      ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
  · left
    refine ⟨v, ?_, rfl⟩
    intro hred
    exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
      ((old_adj_y0_core_iff data v).2 (Or.inr hred))
  · exact False.elim
      ((SimpleGraph.compl_adj _ _ _).1 hysw |>.2
        (old_adj_yStar_a data p))
  · exact False.elim
      ((SimpleGraph.compl_adj _ _ _).1 hysw |>.2
        (old_adj_yStar_b data hG p))
  · right
    left
    refine ⟨r, ?_, ?_, rfl⟩
    · intro hr
      exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        ((old_adj_y0_x_iff data r).2 hr)
    · intro hr
      exact (SimpleGraph.compl_adj _ _ _).1 hysw |>.2
        ((extraAOldGraph data).adj_symm
          ((old_adj_x_yStar_iff data r).2 hr))
  · cases r with
    | none =>
        exact False.elim
          (((SimpleGraph.compl_adj _ _ _).1 hysw).1 rfl)
    | some q =>
        rcases (blue_adj_y0_ySome_iff data hG q).1 hy0w with hq1 | hq2
        · exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hysw |>.2
              ((extraAOldGraph data).adj_symm
                (hq1 ▸ old_adj_y1_yStar data hG)))
        · right
          right
          exact congrArg (fun t ↦
            Switching.Vertex.y data.cert (some t)) hq2
  · exact False.elim
      ((SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        (old_adj_y0_z data))

@[simp]
private theorem old_adj_core_xSome_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (q : Fin (s - 1)) :
    (extraAOldGraph data).Adj (Switching.Vertex.core v)
        (Switching.Vertex.x data.cert (some q)) ↔
      v ≠ data.cert.i q := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]
  exact ne_comm

@[simp]
private theorem old_adj_x_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (r t : Option (Fin (s - 1))) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.x data.cert r)
        (Switching.Vertex.y data.cert t) ↔ r = t := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.outerIndexEquiv]

@[simp]
private theorem old_adj_y2_core_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) :
    (extraAOldGraph data).Adj (y2 data)
        (Switching.Vertex.core v) ↔
      v = i2 data ∨ G.Adj (i2 data) v := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    data.cert.c_ne_i, ne_comm]

private theorem xIn_ab2_some
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (yStar data))
    (r : XIn data.cert K) :
    ∃ q : Fin (s - 1),
      r.1 = some q ∧ q ≠ i0Index data := by
  rcases common_ab2_cases data hG (hKsub r.2) with h | h | h
  · obtain ⟨v, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨t, ht0, htn, heq⟩ := h
    have hrt : r.1 = t :=
      vertex_x_injective data.cert heq
    cases t with
    | none => exact False.elim (htn rfl)
    | some q =>
        refine ⟨q, hrt, ?_⟩
        intro hq
        exact ht0 (congrArg some hq)
  · have := congrArg blockTag h
    simp at this

private theorem yIn_ab2_eq_i2
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (yStar data))
    (r : YIn data.cert K) :
    r.1 = some (i2Index data) := by
  rcases common_ab2_cases data hG (hKsub r.2) with h | h | h
  · obtain ⟨v, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨t, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · exact vertex_y_injective data.cert h

/-- Row A-B2: the newly blue edge `y₀y_*` has no common blue
`K_(s-1)`. -/
theorem blue_common_y0_yStar_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data)ᶜ.CliqueFreeOn
      ((extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (yStar data))
      (s - 1) := by
  classical
  intro K hKsub hK
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab2_cases data hG (hKsub d.2) with h | h | h
    · obtain ⟨v, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hBZero : Fintype.card (BIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab2_cases data hG (hKsub d.2) with h | h | h
    · obtain ⟨v, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_ab2_cases data hG (hKsub d.2) with h | h | h
    · obtain ⟨v, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hYle : Fintype.card (YIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    exact (yIn_ab2_eq_i2 data hG hKsub r).trans
      (yIn_ab2_eq_i2 data hG hKsub t).symm
  let qOf : XIn data.cert K → Fin (s - 1) :=
    fun r ↦ Classical.choose (xIn_ab2_some data hG hKsub r)
  have qOf_spec (r : XIn data.cert K) :
      r.1 = some (qOf r) :=
    (Classical.choose_spec (xIn_ab2_some data hG hKsub r)).1
  have qOf_ne_i0 (r : XIn data.cert K) :
      qOf r ≠ i0Index data :=
    (Classical.choose_spec (xIn_ab2_some data hG hKsub r)).2
  have qOf_inj : Function.Injective qOf := by
    intro r t hrt
    apply Subtype.ext
    rw [qOf_spec r, qOf_spec t, hrt]
  have hparts := card_eq_six_blocks data.cert K
  have hcard := hK.card_eq
  by_cases hXlarge : 2 ≤ Fintype.card (XIn data.cert K)
  · have hCoreZero : Fintype.card (CoreIn K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro d
      have hXatMost : Fintype.card (XIn data.cert K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro r t
        have hdr :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1)
              (Switching.Vertex.x data.cert (some (qOf r))) := by
          rw [← qOf_spec r]
          exact hK.isClique d.2 r.2 (by simp)
        have hdt :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1)
              (Switching.Vertex.x data.cert (some (qOf t))) := by
          rw [← qOf_spec t]
          exact hK.isClique d.2 t.2 (by simp)
        have hr :
            d.1 = data.cert.i (qOf r) := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 hdr |>.2
            ((old_adj_core_xSome_iff data d.1 (qOf r)).2 h)
        have ht :
            d.1 = data.cert.i (qOf t) := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 hdt |>.2
            ((old_adj_core_xSome_iff data d.1 (qOf t)).2 h)
        exact qOf_inj (data.cert.i.injective (hr.symm.trans ht))
      omega
    let T := {q : Fin (s - 1) // q ≠ i0Index data}
    have hi20 : i2Index data ≠ i0Index data := by
      intro h
      have := congrArg Fin.val h
      simp [i0Index, i2Index, Certificates.i0Index',
        Certificates.i2Index'] at this
    let f : (XIn data.cert K ⊕ YIn data.cert K) ↪ T :=
      { toFun
          | Sum.inl r => ⟨qOf r, qOf_ne_i0 r⟩
          | Sum.inr t => ⟨i2Index data, hi20⟩
        inj' := by
          intro x y hxy
          rcases x with r | a <;> rcases y with t | b
          · exact congrArg Sum.inl
              (qOf_inj (congrArg Subtype.val hxy))
          · exfalso
            have hq2 : qOf r = i2Index data :=
              congrArg Subtype.val hxy
            have hblueActual :=
              hK.isClique r.2 b.2 (by simp)
            have hblue :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.x data.cert (some (qOf r)))
                  (y2 data) := by
              simpa [qOf_spec r,
                yIn_ab2_eq_i2 data hG hKsub b] using hblueActual
            exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              ((old_adj_x_y_iff data _ _).2
                (congrArg some hq2))
          · exfalso
            have hq2 : qOf t = i2Index data :=
              (congrArg Subtype.val hxy).symm
            have hblueActual :=
              hK.isClique a.2 t.2 (by simp)
            have hblue :
                (extraAOldGraph data)ᶜ.Adj
                  (y2 data)
                  (Switching.Vertex.x data.cert (some (qOf t))) := by
              simpa [qOf_spec t,
                yIn_ab2_eq_i2 data hG hKsub a] using hblueActual
            exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              ((extraAOldGraph data).adj_symm
                ((old_adj_x_y_iff data _ _).2
                  (congrArg some hq2)))
          · exact congrArg Sum.inr (by
              apply Subtype.ext
              exact (yIn_ab2_eq_i2 data hG hKsub a).trans
                (yIn_ab2_eq_i2 data hG hKsub b).symm) }
    have hXYle :
        Fintype.card (XIn data.cert K) +
            Fintype.card (YIn data.cert K) ≤ s - 2 := by
      have hinj := Fintype.card_le_of_injective f f.injective
      have hTcard : Fintype.card T = s - 2 := by
        dsimp [T]
        rw [Fintype.card_subtype_compl
          (fun q : Fin (s - 1) ↦ q = i0Index data)]
        simp
        have hs := data.cert.five_le_s
        omega
      simpa [hTcard] using hinj
    omega
  · have hXle : Fintype.card (XIn data.cert K) ≤ 1 := by omega
    by_cases hXzero : Fintype.card (XIn data.cert K) = 0
    · by_cases hYzero : Fintype.card (YIn data.cert K) = 0
      · have core_blue_i0 (d : CoreIn K) :
            ¬G.Adj (i0 data) d.1 := by
          rcases common_ab2_cases data hG (hKsub d.2) with h | h | h
          · obtain ⟨v, hblue, heq⟩ := h
            have hdv : d.1 = v := vertex_core_injective heq
            simpa [hdv] using hblue
          · obtain ⟨r, _, _, heq⟩ := h
            have := congrArg blockTag heq
            simp at this
          · have := congrArg blockTag h
            simp at this
        have core_ne_i0 (d : CoreIn K) :
            d.1 ≠ i0 data := by
          intro hdi
          have hblue :=
            (extraAOldGraph data)ᶜ.mem_commonNeighbors.1
              (hKsub d.2) |>.1
          exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
            ((old_adj_y0_core_iff data d.1).2 (Or.inl hdi))
        let f : (CoreIn K ⊕ Unit) ↪ V :=
          { toFun
              | Sum.inl d => d.1
              | Sum.inr _ => i0 data
            inj' := by
              intro x y hxy
              rcases x with d | u <;> rcases y with e | v
              · exact congrArg Sum.inl (Subtype.ext hxy)
              · exact False.elim (core_ne_i0 d hxy)
              · exact False.elim (core_ne_i0 e hxy.symm)
              · cases u
                cases v
                rfl }
        have hproj :
            Fintype.card (CoreIn K ⊕ Unit) < s := by
          apply card_lt_of_cliqueFreeOn_of_embedding
            hG.2.cliqueFreeOn f
          · intro
            exact Set.mem_univ _
          · intro x y hxy
            rcases x with d | u <;> rcases y with e | v
            · have hblue :
                  (extraAOldGraph data)ᶜ.Adj
                    (Switching.Vertex.core d.1)
                    (Switching.Vertex.core e.1) :=
                hK.isClique d.2 e.2 (by
                  intro h
                  apply hxy
                  exact congrArg Sum.inl
                    (Subtype.ext (vertex_core_injective h)))
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨fun h ↦ hxy (congrArg Sum.inl (Subtype.ext h)),
                  fun hred ↦
                    (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
                      ((old_adj_core_core data d.1 e.1).2 hred)⟩
            · cases v
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨core_ne_i0 d,
                  fun hred ↦ core_blue_i0 d (G.adj_symm hred)⟩
            · cases u
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨(core_ne_i0 e).symm, core_blue_i0 e⟩
            · exact False.elim (hxy (by
                cases u
                cases v
                rfl))
        simp at hproj
        have hs := data.cert.five_le_s
        omega
      · have hYone : Fintype.card (YIn data.cert K) = 1 := by omega
        let yelem : YIn data.cert K :=
          Classical.choice (Fintype.card_pos_iff.mp (by omega))
        have hy2 : y2 data ∈ K := by
          have := yelem.2
          simpa [yIn_ab2_eq_i2 data hG hKsub yelem] using this
        have core_blue_i0 (d : CoreIn K) :
            ¬G.Adj (i0 data) d.1 := by
          rcases common_ab2_cases data hG (hKsub d.2) with h | h | h
          · obtain ⟨v, hblue, heq⟩ := h
            have hdv : d.1 = v := vertex_core_injective heq
            simpa [hdv] using hblue
          · obtain ⟨r, _, _, heq⟩ := h
            have := congrArg blockTag heq
            simp at this
          · have := congrArg blockTag h
            simp at this
        have core_ne_i0 (d : CoreIn K) :
            d.1 ≠ i0 data := by
          intro hdi
          have hblue :=
            (extraAOldGraph data)ᶜ.mem_commonNeighbors.1
              (hKsub d.2) |>.1
          exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
            ((old_adj_y0_core_iff data d.1).2 (Or.inl hdi))
        have core_blue_i2 (d : CoreIn K) :
            ¬G.Adj (i2 data) d.1 := by
          intro hred
          have hblue :=
            hK.isClique hy2 d.2 (by simp)
          exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
            ((old_adj_y2_core_iff data d.1).2 (Or.inr hred))
        have core_ne_i2 (d : CoreIn K) :
            d.1 ≠ i2 data := by
          intro hdi
          have hblue :=
            hK.isClique hy2 d.2 (by simp)
          exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
            ((old_adj_y2_core_iff data d.1).2 (Or.inl hdi))
        have hi02Index : i0Index data ≠ i2Index data := by
          intro h
          have := congrArg Fin.val h
          simp [i0Index, i2Index, Certificates.i0Index',
            Certificates.i2Index'] at this
        have hi02 : i0 data ≠ i2 data :=
          fun h ↦ hi02Index (data.cert.i.injective h)
        let f : (CoreIn K ⊕ Bool) ↪ V :=
          { toFun
              | Sum.inl d => d.1
              | Sum.inr false => i0 data
              | Sum.inr true => i2 data
            inj' := by
              intro x y hxy
              rcases x with d | b <;> rcases y with e | c
              · exact congrArg Sum.inl (Subtype.ext hxy)
              · cases c
                · exact False.elim (core_ne_i0 d hxy)
                · exact False.elim (core_ne_i2 d hxy)
              · cases b
                · exact False.elim (core_ne_i0 e hxy.symm)
                · exact False.elim (core_ne_i2 e hxy.symm)
              · cases b <;> cases c
                · rfl
                · exact False.elim (hi02 hxy)
                · exact False.elim (hi02 hxy.symm)
                · rfl }
        have hproj :
            Fintype.card (CoreIn K ⊕ Bool) < s := by
          apply card_lt_of_cliqueFreeOn_of_embedding
            hG.2.cliqueFreeOn f
          · intro
            exact Set.mem_univ _
          · intro x y hxy
            rcases x with d | b <;> rcases y with e | c
            · have hblue :=
                  hK.isClique d.2 e.2 (by
                    intro h
                    apply hxy
                    exact congrArg Sum.inl
                      (Subtype.ext (vertex_core_injective h)))
              exact (SimpleGraph.compl_adj _ _ _).2
                ⟨fun h ↦ hxy (congrArg Sum.inl (Subtype.ext h)),
                  fun hred ↦
                    (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
                      ((old_adj_core_core data d.1 e.1).2 hred)⟩
            · cases c with
              | false =>
                  exact (SimpleGraph.compl_adj _ _ _).2
                    ⟨core_ne_i0 d,
                      fun hred ↦ core_blue_i0 d (G.adj_symm hred)⟩
              | true =>
                  exact (SimpleGraph.compl_adj _ _ _).2
                    ⟨core_ne_i2 d,
                      fun hred ↦ core_blue_i2 d (G.adj_symm hred)⟩
            · cases b with
              | false =>
                  exact (SimpleGraph.compl_adj _ _ _).2
                    ⟨(core_ne_i0 e).symm, core_blue_i0 e⟩
              | true =>
                  exact (SimpleGraph.compl_adj _ _ _).2
                    ⟨(core_ne_i2 e).symm, core_blue_i2 e⟩
            · cases b <;> cases c
              · exact False.elim (hxy rfl)
              · exact data.cert.i_compl_adj hi02Index
              · exact data.cert.i_compl_adj hi02Index.symm
              · exact False.elim (hxy rfl)
        simp at hproj
        have hs := data.cert.five_le_s
        omega
    · have hXone : Fintype.card (XIn data.cert K) = 1 := by omega
      have hCoreLe : Fintype.card (CoreIn K) ≤ 1 := by
        let r : XIn data.cert K :=
          Classical.choice (Fintype.card_pos_iff.mp (by omega))
        rw [Fintype.card_le_one_iff]
        intro d e
        have hdr :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1)
              (Switching.Vertex.x data.cert (some (qOf r))) := by
          rw [← qOf_spec r]
          exact hK.isClique d.2 r.2 (by simp)
        have her :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core e.1)
              (Switching.Vertex.x data.cert (some (qOf r))) := by
          rw [← qOf_spec r]
          exact hK.isClique e.2 r.2 (by simp)
        have hd : d.1 = data.cert.i (qOf r) := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 hdr |>.2
            ((old_adj_core_xSome_iff data d.1 (qOf r)).2 h)
        have he : e.1 = data.cert.i (qOf r) := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 her |>.2
            ((old_adj_core_xSome_iff data e.1 (qOf r)).2 h)
        exact Subtype.ext (hd.trans he.symm)
      have hs := data.cert.five_le_s
      omega

/-! ## Row (A-B3) -/

@[simp]
private theorem old_adj_ySome_a_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.a p) ↔
      p = c0Index data ∧ q ∈ data.cert.T := by
  rw [(extraAOldGraph data).adj_comm,
    extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    data.cert.c_ne_i, and_comm]

@[simp]
private theorem old_adj_ySome_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.b p) ↔
      p ≠ c0Index data ∧
        G.Adj (data.cert.c p) (data.cert.i q) := by
  by_cases hp0 : p = c0Index data
  · subst p
    rw [(extraAOldGraph data).adj_comm,
      extraAOldGraph_adj_iff, Switching.final_adj_iff]
    simp [Switching.preGraph_adj_lower_y_iff,
      Switching.removedRedGraph_adj_iff,
      Switching.addedRedGraph_adj_iff,
      extraARemovedRedRel, extraAAddedRedRel,
      Switching.SymmPair, Canonical.secondCertificateAt,
      data.cert.c_ne_i, data.cert.mem_T]
  · rw [(extraAOldGraph data).adj_comm,
      extraAOldGraph_adj_iff, Switching.final_adj_iff]
    simp [Switching.preGraph_adj_lower_y_iff,
      Switching.removedRedGraph_adj_iff,
      Switching.addedRedGraph_adj_iff,
      extraARemovedRedRel, extraAAddedRedRel,
      Switching.SymmPair, Canonical.secondCertificateAt,
      data.cert.c_ne_i, data.cert.mem_T, hp0]
    exact fun _ ↦ (data.cert.c_ne_i p q).symm

private theorem common_ab3_cases
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {w : Switching.Vertex V k s}
    (hw : w ∈ (extraAOldGraph data)ᶜ.commonNeighbors
      (y0 data) (y2 data)) :
    (∃ v : V,
      v ≠ i0 data ∧ ¬G.Adj (i0 data) v ∧
      v ≠ i2 data ∧ ¬G.Adj (i2 data) v ∧
        w = Switching.Vertex.core v) ∨
    (∃ p : Fin (k - 1),
      p ≠ c0Index data ∧ w = Switching.Vertex.a p) ∨
    w = Switching.Vertex.b (c0Index data) ∨
    (∃ p : Fin (k - 1),
      p ≠ c0Index data ∧
      ¬G.Adj (data.cert.c p) (i0 data) ∧
      ¬G.Adj (data.cert.c p) (i2 data) ∧
        w = Switching.Vertex.b p) ∨
    (∃ r : Option (Fin (s - 1)),
      r ≠ some (i0Index data) ∧
      r ≠ some (i2Index data) ∧
        w = Switching.Vertex.x data.cert r) ∨
      w = yStar data := by
  obtain ⟨hy0w, hy2w⟩ :=
    (extraAOldGraph data)ᶜ.mem_commonNeighbors.1 hw
  rcases vertex_six_block_cases data.cert w with
      ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ |
      ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
  · left
    refine ⟨v, ?_, ?_, ?_, ?_, rfl⟩
    · intro hv
      exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        ((old_adj_y0_core_iff data v).2 (Or.inl hv))
    · intro hred
      exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        ((old_adj_y0_core_iff data v).2 (Or.inr hred))
    · intro hv
      exact (SimpleGraph.compl_adj _ _ _).1 hy2w |>.2
        ((old_adj_y2_core_iff data v).2 (Or.inl hv))
    · intro hred
      exact (SimpleGraph.compl_adj _ _ _).1 hy2w |>.2
        ((old_adj_y2_core_iff data v).2 (Or.inr hred))
  · right
    left
    refine ⟨p, ?_, rfl⟩
    intro hp0
    exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
      ((old_adj_ySome_a_iff data (i0Index data) p).2
        ⟨hp0, (data.cert.mem_T _).2 data.c0_i0_red⟩)
  · by_cases hp0 : p = c0Index data
    · subst p
      exact Or.inr (Or.inr (Or.inl rfl))
    · right
      right
      right
      left
      refine ⟨p, hp0, ?_, ?_, rfl⟩
      · intro hred
        exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
          ((old_adj_ySome_b_iff data (i0Index data) p).2
            ⟨hp0, hred⟩)
      · intro hred
        exact (SimpleGraph.compl_adj _ _ _).1 hy2w |>.2
          ((old_adj_ySome_b_iff data (i2Index data) p).2
            ⟨hp0, hred⟩)
  · right
    right
    right
    right
    left
    refine ⟨r, ?_, ?_, rfl⟩
    · intro hr
      exact (SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        ((extraAOldGraph data).adj_symm
          ((old_adj_x_y_iff data r
            (some (i0Index data))).2 hr))
    · intro hr
      exact (SimpleGraph.compl_adj _ _ _).1 hy2w |>.2
        ((extraAOldGraph data).adj_symm
          ((old_adj_x_y_iff data r
            (some (i2Index data))).2 hr))
  · cases r with
    | none =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | some q =>
        rcases (blue_adj_y0_ySome_iff data hG q).1 hy0w with hq1 | hq2
        · exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hy2w |>.2
              ((extraAOldGraph data).adj_symm
                (hq1 ▸ old_adj_y1_y2 data hG)))
        · subst q
          exact False.elim
            (((SimpleGraph.compl_adj _ _ _).1 hy2w).1 rfl)
  · exact False.elim
      ((SimpleGraph.compl_adj _ _ _).1 hy0w |>.2
        (old_adj_y0_z data))

@[simp]
private theorem old_adj_core_xStar_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core v) (xStar data) ↔
      ¬∃ p ∈ P data, v = data.cert.c p := by
  rw [extraAOldGraph_adj_iff]
  simp [final_adj_core_xStar, extraARemovedRedRel,
    extraAAddedRedRel, Switching.SymmPair]

private theorem old_adj_a_xSome
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.a p)
        (Switching.Vertex.x data.cert (some q)) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt,
    data.cert.c_ne_i, hE]

@[simp]
private theorem old_adj_b_xSome_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.b p)
        (Switching.Vertex.x data.cert (some q)) ↔
      p ≠ c0Index data ∨
        q ≠ Switching.Vertex.i1 data.cert := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, Canonical.secondCertificateAt]
  tauto

@[simp]
private theorem old_adj_core_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (p : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.core v)
        (Switching.Vertex.b p) ↔
      v ≠ data.cert.c p ∧ G.Adj (data.cert.c p) v := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_lower_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, specialLift_adj_core_b]

@[simp]
private theorem old_adj_a_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.a p)
        (Switching.Vertex.b q) ↔ p ≠ q := by
  rw [extraAOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_lower_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraARemovedRedRel, extraAAddedRedRel,
    Switching.SymmPair, specialLift_adj_a_b]

private theorem old_adj_b0_cp_of_mem_P
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp : p ∈ P data) :
    (extraAOldGraph data).Adj
        (Switching.Vertex.b (c0Index data))
        (Switching.Vertex.core (data.cert.c p)) := by
  rw [(extraAOldGraph data).adj_comm, old_adj_core_b_iff]
  have hp0 : p ≠ c0Index data := by
    intro hp0
    subst p
    exact c0_not_mem_P data hp
  exact ⟨fun h ↦ hp0 (data.cert.c.injective h),
    data.cert.c_adj hp0.symm⟩

private theorem core_ab3_spec
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (d : CoreIn K) :
    d.1 ≠ i0 data ∧ ¬G.Adj (i0 data) d.1 ∧
      d.1 ≠ i2 data ∧ ¬G.Adj (i2 data) d.1 := by
  rcases common_ab3_cases data hG (hKsub d.2) with
      h | h | h | h | h | h
  · obtain ⟨v, hv0, hb0, hv2, hb2, heq⟩ := h
    have hdv := vertex_core_injective heq
    simpa [hdv] using And.intro hv0
      (And.intro hb0 (And.intro hv2 hb2))
  · obtain ⟨p, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨p, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨r, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem a_ab3_ne_c0
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (p : AIn K) :
    p.1 ≠ c0Index data := by
  rcases common_ab3_cases data hG (hKsub p.2) with
      h | h | h | h | h | h
  · obtain ⟨v, _, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨q, hq0, heq⟩ := h
    have hpq := vertex_a_injective heq
    simpa [hpq] using hq0
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨q, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨r, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem b_ab3_spec
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (p : BIn K) :
    p.1 = c0Index data ∨
      (p.1 ≠ c0Index data ∧
        ¬G.Adj (data.cert.c p.1) (i0 data) ∧
        ¬G.Adj (data.cert.c p.1) (i2 data)) := by
  rcases common_ab3_cases data hG (hKsub p.2) with
      h | h | h | h | h | h
  · obtain ⟨v, _, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨q, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · exact Or.inl (vertex_b_injective h)
  · obtain ⟨q, hq0, hb0, hb2, heq⟩ := h
    have hpq := vertex_b_injective heq
    have hspec :
        q ≠ c0Index data ∧
          ¬G.Adj (data.cert.c q) (i0 data) ∧
          ¬G.Adj (data.cert.c q) (i2 data) :=
      ⟨hq0, hb0, hb2⟩
    exact Or.inr (by simpa [hpq] using hspec)
  · obtain ⟨r, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem b_ab3_zero_or_large
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (p : BIn K) :
    p.1 = c0Index data ∨ 2 ≤ p.1.val := by
  rcases b_ab3_spec data hG hKsub p with hp0 | hp
  · exact Or.inl hp0
  · right
    by_contra hlarge
    have hpval : p.1.val < 2 := Nat.lt_of_not_ge hlarge
    have hpne0 : p.1.val ≠ 0 := by
      intro hpv
      apply hp.1
      apply Fin.ext
      simpa [c0Index, Certificates.c0Index] using hpv
    have hpval1 : p.1.val = 1 := by omega
    have hp1 : p.1 = c1Index data := by
      apply Fin.ext
      simpa [c1Index, Certificates.c1Index] using hpval1
    exact hp.2.1 (by
      simpa [hp1] using data.c1_i0_red)

private theorem x_ab3_spec
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (r : XIn data.cert K) :
    r.1 ≠ some (i0Index data) ∧
      r.1 ≠ some (i2Index data) := by
  rcases common_ab3_cases data hG (hKsub r.2) with
      h | h | h | h | h | h
  · obtain ⟨v, _, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨p, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨p, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨t, ht0, ht2, heq⟩ := h
    have hrt := vertex_x_injective data.cert heq
    simpa [hrt] using And.intro ht0 ht2
  · have := congrArg blockTag h
    simp at this

private theorem y_ab3_eq_none
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (r : YIn data.cert K) :
    r.1 = none := by
  rcases common_ab3_cases data hG (hKsub r.2) with
      h | h | h | h | h | h
  · obtain ⟨v, _, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨p, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨p, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨t, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · exact vertex_y_injective data.cert h

private theorem card_aIn_ab3_le_one
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K) :
    Fintype.card (AIn K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro p q
  by_contra hpq
  have hpqv :
      (Switching.Vertex.a p.1 : Switching.Vertex V k s) ≠
        Switching.Vertex.a q.1 := by
    intro h
    apply hpq
    exact Subtype.ext (vertex_a_injective h)
  have hblue := hK p.2 q.2 hpqv
  exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
    ((old_adj_a_a_iff data p.1 q.1).2
      (fun h ↦ hpq (Subtype.ext h)))

private theorem card_bIn_ab3_le_two
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K) :
    Fintype.card (BIn K) ≤ 2 := by
  classical
  let f : BIn K ↪ Bool :=
    { toFun := fun p ↦ decide (p.1 = c0Index data)
      inj' := by
        intro p q hpqBool
        by_cases hp0 : p.1 = c0Index data
        · by_cases hq0 : q.1 = c0Index data
          · exact Subtype.ext (hp0.trans hq0.symm)
          · simp [hp0, hq0] at hpqBool
        · by_cases hq0 : q.1 = c0Index data
          · simp [hp0, hq0] at hpqBool
          · apply Subtype.ext
            by_contra hpq
            have hpLarge :=
              (b_ab3_zero_or_large data hG hKsub p).resolve_left hp0
            have hqLarge :=
              (b_ab3_zero_or_large data hG hKsub q).resolve_left hq0
            have hpqv :
                (Switching.Vertex.b p.1 :
                    Switching.Vertex V k s) ≠
                  Switching.Vertex.b q.1 := by
              intro h
              exact hpq (vertex_b_injective h)
            have hblue := hK p.2 q.2 hpqv
            exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              ((old_adj_b_b_iff data p.1 q.1).2
                (Or.inl ⟨hpq,
                  Or.inr ⟨hpLarge, hqLarge⟩⟩)) }
  simpa using Fintype.card_le_of_injective f f.injective

private theorem card_yIn_ab3_le_one
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data)) :
    Fintype.card (YIn data.cert K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro r t
  apply Subtype.ext
  exact (y_ab3_eq_none data hG hKsub r).trans
    (y_ab3_eq_none data hG hKsub t).symm

private theorem card_zIn_ab3_eq_zero
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data)) :
    Fintype.card (ZIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro z
  rcases common_ab3_cases data hG (hKsub z.2) with
      h | h | h | h | h | h
  · obtain ⟨v, _, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨p, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this
  · obtain ⟨p, _, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨r, _, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem card_ab3_many_x_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXlarge : 2 ≤ Fintype.card (XIn data.cert K)) :
    K.card ≤ s - 2 := by
  classical
  obtain ⟨r₀, t₀, hrt⟩ :=
    Fintype.one_lt_card_iff.mp (by omega :
      1 < Fintype.card (XIn data.cert K))
  have hCoreZero : Fintype.card (CoreIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    have hdr :
        (extraAOldGraph data)ᶜ.Adj
          (Switching.Vertex.core d.1)
          (Switching.Vertex.x data.cert r₀.1) :=
      hK d.2 r₀.2 (by simp)
    have hdt :
        (extraAOldGraph data)ᶜ.Adj
          (Switching.Vertex.core d.1)
          (Switching.Vertex.x data.cert t₀.1) :=
      hK d.2 t₀.2 (by simp)
    cases hr : r₀.1 with
    | none =>
        cases ht : t₀.1 with
        | none =>
            apply hrt
            apply Subtype.ext
            rw [hr, ht]
        | some q =>
            have hdtSome :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.core d.1)
                  (Switching.Vertex.x data.cert (some q)) := by
              simpa [ht] using hdt
            have hdq : d.1 = data.cert.i q := by
              by_contra h
              exact (SimpleGraph.compl_adj _ _ _).1 hdtSome |>.2
                ((old_adj_core_xSome_iff data d.1 q).2 h)
            have hred :
                (extraAOldGraph data).Adj
                  (Switching.Vertex.core d.1) (xStar data) := by
              rw [old_adj_core_xStar_iff]
              rintro ⟨p, hp, hdp⟩
              exact data.cert.c_ne_i p q (hdp.symm.trans hdq)
            have hdr' :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.core d.1) (xStar data) := by
              simpa [hr] using hdr
            exact (SimpleGraph.compl_adj _ _ _).1 hdr' |>.2 hred
    | some q =>
        have hdrSome :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1)
              (Switching.Vertex.x data.cert (some q)) := by
          simpa [hr] using hdr
        cases ht : t₀.1 with
        | none =>
            have hdq : d.1 = data.cert.i q := by
              by_contra h
              exact (SimpleGraph.compl_adj _ _ _).1 hdrSome |>.2
                ((old_adj_core_xSome_iff data d.1 q).2 h)
            have hred :
                (extraAOldGraph data).Adj
                  (Switching.Vertex.core d.1) (xStar data) := by
              rw [old_adj_core_xStar_iff]
              rintro ⟨p, hp, hdp⟩
              exact data.cert.c_ne_i p q (hdp.symm.trans hdq)
            have hdt' :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.core d.1) (xStar data) := by
              simpa [ht] using hdt
            exact (SimpleGraph.compl_adj _ _ _).1 hdt' |>.2 hred
        | some t =>
            have hdtSome :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.core d.1)
                  (Switching.Vertex.x data.cert (some t)) := by
              simpa [ht] using hdt
            have hdq : d.1 = data.cert.i q := by
              by_contra h
              exact (SimpleGraph.compl_adj _ _ _).1 hdrSome |>.2
                ((old_adj_core_xSome_iff data d.1 q).2 h)
            have hdtq : d.1 = data.cert.i t := by
              by_contra h
              exact (SimpleGraph.compl_adj _ _ _).1 hdtSome |>.2
                ((old_adj_core_xSome_iff data d.1 t).2 h)
            have hqt : q = t :=
              data.cert.i.injective (hdq.symm.trans hdtq)
            apply hrt
            apply Subtype.ext
            rw [hr, ht, hqt]
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro p
    have hp0 := a_ab3_ne_c0 data hG hKsub p
    have hblue := hK p.2 r₀.2 (by simp)
    cases hr : r₀.1 with
    | none =>
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          (by simpa [hr] using
            (old_adj_a_xStar_iff data p.1).2 hp0)
    | some q =>
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          (by simpa [hr] using old_adj_a_xSome data hG p.1 q)
  have hBonly0 : ∀ p : BIn K, p.1 = c0Index data := by
    intro p
    rcases b_ab3_spec data hG hKsub p with hp0 | hp
    · exact hp0
    · have hblue := hK p.2 r₀.2 (by simp)
      cases hr : r₀.1 with
      | none =>
          exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              (by simpa [hr] using
                (old_adj_b_xStar_iff data p.1).2 hp.1))
      | some q =>
          have hred :
              (extraAOldGraph data).Adj
                (Switching.Vertex.b p.1)
                (Switching.Vertex.x data.cert (some q)) :=
            (old_adj_b_xSome_iff data p.1 q).2
              (Or.inl hp.1)
          exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              (by simpa [hr] using hred))
  have hBle : Fintype.card (BIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    exact Subtype.ext ((hBonly0 p).trans (hBonly0 q).symm)
  have hYle := card_yIn_ab3_le_one data hG hKsub
  have hZZero := card_zIn_ab3_eq_zero data hG hKsub
  have hparts := card_eq_six_blocks data.cert K
  by_cases hBZero : Fintype.card (BIn K) = 0
  · let Allowed :=
      {r : Option (Fin (s - 1)) //
        ¬(r = some (i0Index data) ∨
          r = some (i2Index data))}
    let f : (XIn data.cert K ⊕ YIn data.cert K) ↪ Allowed :=
      { toFun
          | Sum.inl r => ⟨r.1, by
              simpa [not_or] using x_ab3_spec data hG hKsub r⟩
          | Sum.inr _ => ⟨none, by simp⟩
        inj' := by
          intro x y hxy
          rcases x with r | a <;> rcases y with t | b
          · have hval : r.1 = t.1 :=
              congrArg (fun z : Allowed ↦ z.1) hxy
            exact congrArg Sum.inl (Subtype.ext hval)
          · exfalso
            have hrnone : r.1 = none :=
              congrArg Subtype.val hxy
            have hbnone := y_ab3_eq_none data hG hKsub b
            have hne :
                Switching.Vertex.x data.cert r.1 ≠
                  Switching.Vertex.y data.cert b.1 := by
              intro h
              simpa using congrArg blockTag h
            have hblue := hK r.2 b.2 hne
            have hblue' :
                (extraAOldGraph data)ᶜ.Adj
                  (xStar data) (yStar data) := by
              simpa [hrnone, hbnone] using hblue
            exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
              ((old_adj_xStar_y_iff data none).2 rfl)
          · exfalso
            have htnone : t.1 = none :=
              (congrArg Subtype.val hxy).symm
            have hanone := y_ab3_eq_none data hG hKsub a
            have hne :
                Switching.Vertex.y data.cert a.1 ≠
                  Switching.Vertex.x data.cert t.1 := by
              intro h
              simpa using congrArg blockTag h
            have hblue := hK a.2 t.2 hne
            have hblue' :
                (extraAOldGraph data)ᶜ.Adj
                  (yStar data) (xStar data) := by
              simpa [htnone, hanone] using hblue
            exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
              ((extraAOldGraph data).adj_symm
                ((old_adj_xStar_y_iff data none).2 rfl))
          · exact congrArg Sum.inr (by
              apply Subtype.ext
              exact (y_ab3_eq_none data hG hKsub a).trans
                (y_ab3_eq_none data hG hKsub b).symm) }
    have hAllowed : Fintype.card Allowed = s - 2 := by
      have hi02 : i0Index data ≠ i2Index data := by
        intro h
        have := congrArg Fin.val h
        simp [i0Index, i2Index, Certificates.i0Index',
          Certificates.i2Index'] at this
      let Forbidden :=
        {r : Option (Fin (s - 1)) //
          r = some (i0Index data) ∨
            r = some (i2Index data)}
      let e : Forbidden ≃ Bool :=
        { toFun := fun r ↦
            if r.1 = some (i0Index data) then false else true
          invFun
            | false => ⟨some (i0Index data), Or.inl rfl⟩
            | true => ⟨some (i2Index data), Or.inr rfl⟩
          left_inv := by
            intro r
            rcases r.2 with hr | hr
            · apply Subtype.ext
              simp [hr]
            · apply Subtype.ext
              simp [hr, hi02.symm]
          right_inv := by
            intro b
            cases b <;> simp [hi02, hi02.symm] }
      have hForbidden : Fintype.card Forbidden = 2 := by
        rw [Fintype.card_congr e]
        decide
      dsimp [Allowed]
      rw [Fintype.card_subtype_compl
        (fun r : Option (Fin (s - 1)) ↦
          r = some (i0Index data) ∨
            r = some (i2Index data))]
      change Fintype.card (Option (Fin (s - 1))) -
          Fintype.card Forbidden = s - 2
      rw [hForbidden]
      simp
      have hs := data.cert.five_le_s
      omega
    have hXYle :
        Fintype.card (XIn data.cert K) +
            Fintype.card (YIn data.cert K) ≤ s - 2 := by
      have hinj := Fintype.card_le_of_injective f f.injective
      simpa [hAllowed] using hinj
    omega
  · have hBpos : 0 < Fintype.card (BIn K) := by omega
    let b₀ : BIn K :=
      Classical.choice (Fintype.card_pos_iff.mp hBpos)
    have hb0 : b₀.1 = c0Index data := hBonly0 b₀
    have hYZero : Fintype.card (YIn data.cert K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro y
      have hblue := hK b₀.2 y.2 (by simp)
      have hblue' :
          (extraAOldGraph data)ᶜ.Adj
            (Switching.Vertex.b (c0Index data)) (yStar data) := by
        simpa [hb0, y_ab3_eq_none data hG hKsub y] using hblue
      exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
        ((extraAOldGraph data).adj_symm
          (old_adj_yStar_b data hG (c0Index data)))
    have hXle : Fintype.card (XIn data.cert K) ≤ 2 := by
      let f : XIn data.cert K ↪ Bool :=
        { toFun := fun r ↦ decide (r.1 = none)
          inj' := by
            intro r t hrt
            by_cases hr : r.1 = none
            · by_cases ht : t.1 = none
              · exact Subtype.ext (hr.trans ht.symm)
              · simp [hr, ht] at hrt
            · by_cases ht : t.1 = none
              · simp [hr, ht] at hrt
              · apply Subtype.ext
                have hr1 :
                    r.1 = some (Switching.Vertex.i1 data.cert) := by
                  cases hrq : r.1 with
                  | none => exact False.elim (hr hrq)
                  | some q =>
                      have hblue := hK b₀.2 r.2 (by simp)
                      have hnred :=
                        (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
                      have : q =
                          Switching.Vertex.i1 data.cert := by
                        by_contra hq1
                        exact hnred (by
                          simpa [hb0, hrq] using
                            (old_adj_b_xSome_iff data
                              (c0Index data) q).2
                                (Or.inr hq1))
                      simpa [hrq, this]
                have ht1 :
                    t.1 = some (Switching.Vertex.i1 data.cert) := by
                  cases htq : t.1 with
                  | none => exact False.elim (ht htq)
                  | some q =>
                      have hblue := hK b₀.2 t.2 (by simp)
                      have hnred :=
                        (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
                      have : q =
                          Switching.Vertex.i1 data.cert := by
                        by_contra hq1
                        exact hnred (by
                          simpa [hb0, htq] using
                            (old_adj_b_xSome_iff data
                              (c0Index data) q).2
                                (Or.inr hq1))
                      simpa [htq, this]
                exact hr1.trans ht1.symm }
      simpa using Fintype.card_le_of_injective f f.injective
    have hs := data.cert.five_le_s
    omega

private theorem card_ab3_one_x_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXone : Fintype.card (XIn data.cert K) = 1) :
    K.card ≤ s - 2 := by
  classical
  let x₀ : XIn data.cert K :=
    Classical.choice (Fintype.card_pos_iff.mp (by omega))
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro p
    have hp0 := a_ab3_ne_c0 data hG hKsub p
    have hblue := hK p.2 x₀.2 (by simp)
    cases hx : x₀.1 with
    | none =>
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          (by simpa [hx] using
            (old_adj_a_xStar_iff data p.1).2 hp0)
    | some q =>
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          (by simpa [hx] using old_adj_a_xSome data hG p.1 q)
  have hBonly0 : ∀ p : BIn K, p.1 = c0Index data := by
    intro p
    rcases b_ab3_spec data hG hKsub p with hp0 | hp
    · exact hp0
    · have hblue := hK p.2 x₀.2 (by simp)
      cases hx : x₀.1 with
      | none =>
          exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              (by simpa [hx] using
                (old_adj_b_xStar_iff data p.1).2 hp.1))
      | some q =>
          have hred :
              (extraAOldGraph data).Adj
                (Switching.Vertex.b p.1)
                (Switching.Vertex.x data.cert (some q)) :=
            (old_adj_b_xSome_iff data p.1 q).2
              (Or.inl hp.1)
          exact False.elim
            ((SimpleGraph.compl_adj _ _ _).1 hblue |>.2
              (by simpa [hx] using hred))
  have hBle : Fintype.card (BIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    exact Subtype.ext ((hBonly0 p).trans (hBonly0 q).symm)
  have hYle := card_yIn_ab3_le_one data hG hKsub
  have hZZero := card_zIn_ab3_eq_zero data hG hKsub
  have hparts := card_eq_six_blocks data.cert K
  cases hx : x₀.1 with
  | some q =>
      have hCoreLe : Fintype.card (CoreIn K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro d e
        have hdx :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1)
              (Switching.Vertex.x data.cert (some q)) := by
          have := hK d.2 x₀.2 (by simp)
          simpa [hx] using this
        have hex :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core e.1)
              (Switching.Vertex.x data.cert (some q)) := by
          have := hK e.2 x₀.2 (by simp)
          simpa [hx] using this
        have hd : d.1 = data.cert.i q := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 hdx |>.2
            ((old_adj_core_xSome_iff data d.1 q).2 h)
        have he : e.1 = data.cert.i q := by
          by_contra h
          exact (SimpleGraph.compl_adj _ _ _).1 hex |>.2
            ((old_adj_core_xSome_iff data e.1 q).2 h)
        exact Subtype.ext (hd.trans he.symm)
      have hBYle :
          Fintype.card (BIn K) +
              Fintype.card (YIn data.cert K) ≤ 1 := by
        by_cases hBZero : Fintype.card (BIn K) = 0
        · omega
        · have hBpos : 0 < Fintype.card (BIn K) := by omega
          let b₀ : BIn K :=
            Classical.choice (Fintype.card_pos_iff.mp hBpos)
          have hb0 := hBonly0 b₀
          have hYZero : Fintype.card (YIn data.cert K) = 0 := by
            rw [Fintype.card_eq_zero_iff]
            constructor
            intro y
            have hblue := hK b₀.2 y.2 (by simp)
            have hblue' :
                (extraAOldGraph data)ᶜ.Adj
                  (Switching.Vertex.b (c0Index data))
                  (yStar data) := by
              simpa [hb0, y_ab3_eq_none data hG hKsub y] using hblue
            exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
              ((extraAOldGraph data).adj_symm
                (old_adj_yStar_b data hG (c0Index data)))
          omega
      have hs := data.cert.five_le_s
      omega
  | none =>
      have hYZero : Fintype.card (YIn data.cert K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro y
        have hblue := hK x₀.2 y.2 (by simp)
        have hblue' :
            (extraAOldGraph data)ᶜ.Adj (xStar data) (yStar data) := by
          simpa [hx, y_ab3_eq_none data hG hKsub y] using hblue
        exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
          ((old_adj_xStar_y_iff data none).2 rfl)
      have core_is_P :
          ∀ d : CoreIn K,
            ∃ p ∈ P data, d.1 = data.cert.c p := by
        intro d
        have hblue := hK d.2 x₀.2 (by simp)
        have hblue' :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.core d.1) (xStar data) := by
          simpa [hx] using hblue
        by_contra hnone
        exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
          ((old_adj_core_xStar_iff data d.1).2 hnone)
      have hCoreLe : Fintype.card (CoreIn K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro d e
        obtain ⟨p, hpP, hdp⟩ := core_is_P d
        obtain ⟨q, hqP, heq⟩ := core_is_P e
        by_contra hde
        have hpq : p ≠ q := by
          intro hpq
          subst q
          apply hde
          apply Subtype.ext
          exact hdp.trans heq.symm
        have hblue := hK d.2 e.2 (by
          intro h
          apply hde
          exact Subtype.ext (vertex_core_injective h))
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          ((old_adj_core_core data d.1 e.1).2
            (by simpa [hdp, heq] using data.cert.c_adj hpq))
      have hCoreZero_of_B :
          0 < Fintype.card (BIn K) →
            Fintype.card (CoreIn K) = 0 := by
        intro hBpos
        let b₀ : BIn K :=
          Classical.choice (Fintype.card_pos_iff.mp hBpos)
        have hb0 := hBonly0 b₀
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro d
        obtain ⟨p, hpP, hdp⟩ := core_is_P d
        have hblue := hK b₀.2 d.2 (by simp)
        have hblue' :
            (extraAOldGraph data)ᶜ.Adj
              (Switching.Vertex.b (c0Index data))
              (Switching.Vertex.core (data.cert.c p)) := by
          simpa [hb0, hdp] using hblue
        exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
          (old_adj_b0_cp_of_mem_P data p hpP)
      by_cases hBZero : Fintype.card (BIn K) = 0
      · have hs := data.cert.five_le_s
        omega
      · have hBpos : 0 < Fintype.card (BIn K) := by omega
        have hCoreZero := hCoreZero_of_B hBpos
        have hs := data.cert.five_le_s
        omega

private theorem card_ab3_no_x_with_y_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYPos : 0 < Fintype.card (YIn data.cert K)) :
    K.card ≤ s - 2 := by
  classical
  let y₀ : YIn data.cert K :=
    Classical.choice (Fintype.card_pos_iff.mp hYPos)
  have hyStar : y₀.1 = none :=
    y_ab3_eq_none data hG hKsub y₀
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro a
    have hblue := hK y₀.2 a.2 (by simp)
    have hblue' :
        (extraAOldGraph data)ᶜ.Adj
          (yStar data) (Switching.Vertex.a a.1) := by
      simpa [hyStar] using hblue
    exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
      (old_adj_yStar_a data a.1)
  have hBZero : Fintype.card (BIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro b
    have hblue := hK y₀.2 b.2 (by simp)
    have hblue' :
        (extraAOldGraph data)ᶜ.Adj
          (yStar data) (Switching.Vertex.b b.1) := by
      simpa [hyStar] using hblue
    exact (SimpleGraph.compl_adj _ _ _).1 hblue' |>.2
      (old_adj_yStar_b data hG b.1)
  have hYOne : Fintype.card (YIn data.cert K) = 1 := by
    have hYLe := card_yIn_ab3_le_one data hG hKsub
    omega
  have hZZero := card_zIn_ab3_eq_zero data hG hKsub
  have hi02Index : i0Index data ≠ i2Index data := by
    intro h
    have := congrArg Fin.val h
    simp [i0Index, i2Index, Certificates.i0Index',
      Certificates.i2Index'] at this
  have hi02 : i0 data ≠ i2 data :=
    fun h ↦ hi02Index (data.cert.i.injective h)
  let f : (CoreIn K ⊕ Bool) ↪ V :=
    { toFun
        | Sum.inl d => d.1
        | Sum.inr false => i0 data
        | Sum.inr true => i2 data
      inj' := by
        intro x y hxy
        rcases x with d | b <;> rcases y with e | c
        · exact congrArg Sum.inl (Subtype.ext hxy)
        · cases c
          · exact False.elim ((core_ab3_spec data hG hKsub d).1 hxy)
          · exact False.elim ((core_ab3_spec data hG hKsub d).2.2.1 hxy)
        · cases b
          · exact False.elim ((core_ab3_spec data hG hKsub e).1 hxy.symm)
          · exact False.elim
              ((core_ab3_spec data hG hKsub e).2.2.1 hxy.symm)
        · cases b <;> cases c
          · rfl
          · exact False.elim (hi02 hxy)
          · exact False.elim (hi02 hxy.symm)
          · rfl }
  have hproj : Fintype.card (CoreIn K ⊕ Bool) < s := by
    apply card_lt_of_cliqueFreeOn_of_embedding
      hG.2.cliqueFreeOn f
    · intro
      exact Set.mem_univ _
    · intro x y hxy
      rcases x with d | b <;> rcases y with e | c
      · have hblue :=
          hK d.2 e.2 (by
            intro h
            apply hxy
            exact congrArg Sum.inl
              (Subtype.ext (vertex_core_injective h)))
        exact (SimpleGraph.compl_adj _ _ _).2
          ⟨fun h ↦ hxy (congrArg Sum.inl (Subtype.ext h)),
            fun hred ↦
              (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
                ((old_adj_core_core data d.1 e.1).2 hred)⟩
      · cases c with
        | false =>
            exact (SimpleGraph.compl_adj _ _ _).2
              ⟨(core_ab3_spec data hG hKsub d).1,
                fun hred ↦
                  (core_ab3_spec data hG hKsub d).2.1
                    (G.adj_symm hred)⟩
        | true =>
            exact (SimpleGraph.compl_adj _ _ _).2
              ⟨(core_ab3_spec data hG hKsub d).2.2.1,
                fun hred ↦
                  (core_ab3_spec data hG hKsub d).2.2.2
                    (G.adj_symm hred)⟩
      · cases b with
        | false =>
            exact (SimpleGraph.compl_adj _ _ _).2
              ⟨(core_ab3_spec data hG hKsub e).1.symm,
                (core_ab3_spec data hG hKsub e).2.1⟩
        | true =>
            exact (SimpleGraph.compl_adj _ _ _).2
              ⟨(core_ab3_spec data hG hKsub e).2.2.1.symm,
                (core_ab3_spec data hG hKsub e).2.2.2⟩
      · cases b <;> cases c
        · exact False.elim (hxy rfl)
        · exact data.cert.i_compl_adj hi02Index
        · exact data.cert.i_compl_adj hi02Index.symm
        · exact False.elim (hxy rfl)
  have hparts := card_eq_six_blocks data.cert K
  simp at hproj
  have hs := data.cert.five_le_s
  omega

private def ab3BaseProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core d)) => .core d
  | .inl (.core (.a p)) => .a p
  | .inl (.core (.b p)) => .b p
  | _ => .core (i0 data)

@[simp]
private theorem ab3BaseProjection_core
    (data : Certificates.PlusCaseAData G k s) (d : V) :
    ab3BaseProjection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem ab3BaseProjection_a
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    ab3BaseProjection data (Switching.Vertex.a p) = .a p :=
  rfl

@[simp]
private theorem ab3BaseProjection_b
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    ab3BaseProjection data (Switching.Vertex.b p) = .b p :=
  rfl

private def ab3ReplaceProjection
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core d)) => .core d
  | .inl (.core (.a q)) => .a q
  | .inl (.core (.b q)) =>
      if q = c0Index data then .a p else .b q
  | _ => .core (i0 data)

@[simp]
private theorem ab3ReplaceProjection_core
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (d : V) :
    ab3ReplaceProjection data p (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem ab3ReplaceProjection_a
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    ab3ReplaceProjection data p (Switching.Vertex.a q) = .a q :=
  rfl

@[simp]
private theorem ab3ReplaceProjection_b0
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    ab3ReplaceProjection data p
        (Switching.Vertex.b (c0Index data)) = .a p := by
  simp [ab3ReplaceProjection]

@[simp]
private theorem ab3ReplaceProjection_b_of_ne
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) (hq0 : q ≠ c0Index data) :
    ab3ReplaceProjection data p (Switching.Vertex.b q) = .b q := by
  simp [ab3ReplaceProjection, hq0]

private theorem ab3_no_xy_member_cases
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    {u : Switching.Vertex V k s} (hu : u ∈ K) :
    (∃ d : V, u = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), u = Switching.Vertex.a p) ∨
    (∃ p : Fin (k - 1), u = Switching.Vertex.b p) := by
  rcases common_ab3_cases data hG (hKsub hu) with
      h | h | h | h | h | h
  · obtain ⟨d, _, _, _, _, heq⟩ := h
    exact Or.inl ⟨d, heq⟩
  · obtain ⟨p, _, heq⟩ := h
    exact Or.inr (Or.inl ⟨p, heq⟩)
  · exact Or.inr (Or.inr ⟨c0Index data, h⟩)
  · obtain ⟨p, _, _, _, heq⟩ := h
    exact Or.inr (Or.inr ⟨p, heq⟩)
  · obtain ⟨r, _, _, heq⟩ := h
    have hpos : 0 < Fintype.card (XIn data.cert K) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨r, by simpa [heq] using hu⟩⟩
    omega
  · have hpos : 0 < Fintype.card (YIn data.cert K) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨none, by simpa [h] using hu⟩⟩
    omega

private theorem card_ab3_of_projection
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (f : Switching.Vertex V k s → SpecialLiftVertex V k)
    (hmaps :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data)ᶜ.Adj u v →
          (specialLift G data.cert.c)ᶜ.Adj (f u) (f v))
    (hend :
      ∀ ⦃u⦄, u ∈ K →
        (specialLift G data.cert.c)ᶜ.Adj
          (f u) (.core (i0 data)) ∧
        (specialLift G data.cert.c)ᶜ.Adj
          (f u) (.core (i2 data))) :
    K.card ≤ s - 2 := by
  classical
  let proj : ({u // u ∈ K} ⊕ Bool) →
      SpecialLiftVertex V k
    | Sum.inl u => f u.1
    | Sum.inr false => .core (i0 data)
    | Sum.inr true => .core (i2 data)
  have hi02Index : i0Index data ≠ i2Index data := by
    intro h
    have := congrArg Fin.val h
    simp [i0Index, i2Index, Certificates.i0Index',
      Certificates.i2Index'] at this
  have hclique :
      ∀ x y : ({u // u ∈ K} ⊕ Bool), x ≠ y →
        (specialLift G data.cert.c)ᶜ.Adj (proj x) (proj y) := by
    intro x y hxy
    rcases x with u | b <;> rcases y with v | c
    · apply hmaps u.2 v.2
      apply hK u.2 v.2
      intro huv
      apply hxy
      exact congrArg Sum.inl (Subtype.ext huv)
    · cases c
      · exact (hend u.2).1
      · exact (hend u.2).2
    · cases b
      · exact (specialLift G data.cert.c)ᶜ.adj_symm
          (hend v.2).1
      · exact (specialLift G data.cert.c)ᶜ.adj_symm
          (hend v.2).2
    · cases b <;> cases c
      · exact False.elim (hxy rfl)
      · simpa [proj] using data.cert.i_compl_adj hi02Index
      · simpa [proj] using data.cert.i_compl_adj hi02Index.symm
      · exact False.elim (hxy rfl)
  let emb : ({u // u ∈ K} ⊕ Bool) ↪
      SpecialLiftVertex V k :=
    { toFun := proj
      inj' := by
        intro x y hxy
        by_contra hne
        exact (hclique x y hne).ne hxy }
  have hFirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  have hproj :
      Fintype.card ({u // u ∈ K} ⊕ Bool) < s + 1 :=
    card_lt_of_cliqueFreeOn_of_embedding
      hFirst.2.cliqueFreeOn emb
      (fun _ ↦ Set.mem_univ _) hclique
  simp at hproj
  have hs := data.cert.five_le_s
  omega

private theorem ab3BaseProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data)ᶜ.Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (ab3BaseProjection data u) (ab3BaseProjection data v) := by
  rcases ab3_no_xy_member_cases
      data hG hKsub hXZero hYZero hu with
      ⟨d, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases ab3_no_xy_member_cases
      data hG hKsub hXZero hYZero hv with
      ⟨e, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · simpa only [ab3BaseProjection_core,
      specialLift_compl_adj_core_core] using
        (show Gᶜ.Adj d e from
          (SimpleGraph.compl_adj _ _ _).2
            ⟨fun h ↦ huv.ne (congrArg Switching.Vertex.core h),
              fun hred ↦
                (SimpleGraph.compl_adj _ _ _).1 huv |>.2
                  ((old_adj_core_core data d e).2 hred)⟩)
  ·
    rw [ab3BaseProjection_core, ab3BaseProjection_a,
      specialLift_compl_adj_core_a]
    intro h
    exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
      ((old_adj_core_a data d q).2 (Or.inl h))
  ·
    rw [ab3BaseProjection_core, ab3BaseProjection_b,
      specialLift_compl_adj_core_b]
    by_cases hEq : d = data.cert.c q
    · exact Or.inl hEq
    · right
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨Ne.symm hEq, fun hred ↦
          (SimpleGraph.compl_adj _ _ _).1 huv |>.2
            ((old_adj_core_b_iff data d q).2 ⟨hEq, hred⟩)⟩
  ·
    rw [ab3BaseProjection_a, ab3BaseProjection_core,
      specialLift_compl_adj_a_core]
    intro h
    exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
      ((old_adj_a_core data p e).2 (Or.inl h))
  ·
    exfalso
    by_cases hpq : p = q
    · subst q
      exact (extraAOldGraph data)ᶜ.loopless.irrefl _ huv
    · exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
        ((old_adj_a_a_iff data p q).2 hpq)
  ·
    rw [ab3BaseProjection_a, ab3BaseProjection_b,
      specialLift_compl_adj_a_b]
    by_contra hpq
    exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
      ((old_adj_a_b_iff data p q).2 hpq)
  ·
    rw [ab3BaseProjection_b, ab3BaseProjection_core,
      specialLift_compl_adj_b_core]
    by_cases hEq : e = data.cert.c p
    · exact Or.inl hEq
    · right
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨Ne.symm hEq, fun hred ↦
          (SimpleGraph.compl_adj _ _ _).1 huv |>.2
            ((extraAOldGraph data).adj_symm
              ((old_adj_core_b_iff data e p).2 ⟨hEq, hred⟩))⟩
  ·
    rw [ab3BaseProjection_b, ab3BaseProjection_a,
      specialLift_compl_adj_b_a]
    by_contra hqp
    exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
      ((extraAOldGraph data).adj_symm
        ((old_adj_a_b_iff data q p).2 hqp))
  ·
    rw [ab3BaseProjection_b, ab3BaseProjection_b,
      specialLift_compl_adj_b_b]
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact (extraAOldGraph data)ᶜ.loopless.irrefl _ huv
    refine ⟨hpq, ?_⟩
    intro hsame
    exact (SimpleGraph.compl_adj _ _ _).1 huv |>.2
      ((old_adj_b_b_iff data p q).2
        (Or.inl ⟨hpq, hsame⟩))

private theorem ab3BaseProjection_adjoins_endpoints
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hb0 : Switching.Vertex.b (c0Index data) ∉ K)
    {u : Switching.Vertex V k s} (hu : u ∈ K) :
    (specialLift G data.cert.c)ᶜ.Adj
        (ab3BaseProjection data u) (.core (i0 data)) ∧
      (specialLift G data.cert.c)ᶜ.Adj
        (ab3BaseProjection data u) (.core (i2 data)) := by
  rcases ab3_no_xy_member_cases
      data hG hKsub hXZero hYZero hu with
      ⟨d, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  ·
    have hd := core_ab3_spec data hG hKsub
      (⟨d, hu⟩ : CoreIn K)
    constructor
    · rw [ab3BaseProjection_core,
        specialLift_compl_adj_core_core]
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨hd.1, fun hred ↦ hd.2.1 (G.adj_symm hred)⟩
    · rw [ab3BaseProjection_core,
        specialLift_compl_adj_core_core]
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨hd.2.2.1, fun hred ↦ hd.2.2.2 (G.adj_symm hred)⟩
  ·
    constructor
    · rw [ab3BaseProjection_a, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i p (i0Index data)
    · rw [ab3BaseProjection_a, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i p (i2Index data)
  ·
    have hp0 : p ≠ c0Index data := by
      intro hp0
      subst p
      exact hb0 hu
    have hp := (b_ab3_spec data hG hKsub
      (⟨p, hu⟩ : BIn K)).resolve_left hp0
    constructor
    · rw [ab3BaseProjection_b, specialLift_compl_adj_b_core]
      exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨data.cert.c_ne_i p (i0Index data), hp.2.1⟩)
    · rw [ab3BaseProjection_b, specialLift_compl_adj_b_core]
      exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨data.cert.c_ne_i p (i2Index data), hp.2.2⟩)

private theorem card_ab3_no_xy_no_b0_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hb0 : Switching.Vertex.b (c0Index data) ∉ K) :
    K.card ≤ s - 2 := by
  exact card_ab3_of_projection data hG hK
    (ab3BaseProjection data)
    (fun {_ _} hu hv huv ↦
      ab3BaseProjection_maps_adj data hG hKsub
        hXZero hYZero hu hv huv)
    (fun {_} hu ↦
      ab3BaseProjection_adjoins_endpoints data hG hKsub
        hXZero hYZero hb0 hu)

private theorem old_adj_b0_cp_of_ne
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (hp0 : p ≠ c0Index data) :
    (extraAOldGraph data).Adj
      (Switching.Vertex.b (c0Index data))
      (Switching.Vertex.core (data.cert.c p)) := by
  rw [(extraAOldGraph data).adj_comm, old_adj_core_b_iff]
  exact ⟨fun h ↦ hp0 (data.cert.c.injective h),
    data.cert.c_adj hp0.symm⟩

private theorem ab3_no_a_of_b0
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hb0 : Switching.Vertex.b (c0Index data) ∈ K)
    (p : Fin (k - 1)) :
    Switching.Vertex.a p ∉ K := by
  intro hp
  have hp0 := a_ab3_ne_c0 data hG hKsub
    (⟨p, hp⟩ : AIn K)
  have hblue := hK hp hb0 (by simp)
  exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
    ((old_adj_a_b_iff data p (c0Index data)).2 hp0)

private theorem ab3Replace_member_cases
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hA : ∀ q : Fin (k - 1), Switching.Vertex.a q ∉ K)
    (p : Fin (k - 1))
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K →
        q = c0Index data ∨ q = p)
    {u : Switching.Vertex V k s} (hu : u ∈ K) :
    (∃ d : V, u = Switching.Vertex.core d) ∨
    u = Switching.Vertex.b (c0Index data) ∨
    (p ≠ c0Index data ∧ u = Switching.Vertex.b p) := by
  rcases ab3_no_xy_member_cases
      data hG hKsub hXZero hYZero hu with
      ⟨d, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact Or.inl ⟨d, rfl⟩
  · exact False.elim (hA q hu)
  · rcases hB q hu with hq0 | hqp
    · subst q
      exact Or.inr (Or.inl rfl)
    · subst q
      by_cases hp0 : p = c0Index data
      · subst p
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hp0, rfl⟩)

private theorem ab3ReplaceProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hA : ∀ q : Fin (k - 1), Switching.Vertex.a q ∉ K)
    (p : Fin (k - 1))
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K →
        q = c0Index data ∨ q = p)
    (hcp : Switching.Vertex.core (data.cert.c p) ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data)ᶜ.Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (ab3ReplaceProjection data p u)
      (ab3ReplaceProjection data p v) := by
  rcases ab3Replace_member_cases
      data hG hKsub hXZero hYZero hA p hB hu with
      ⟨d, rfl⟩ | rfl | ⟨hp0, rfl⟩ <;>
    rcases ab3Replace_member_cases
      data hG hKsub hXZero hYZero hA p hB hv with
      ⟨e, rfl⟩ | rfl | ⟨hp0', rfl⟩
  ·
    rw [ab3ReplaceProjection_core, ab3ReplaceProjection_core,
      specialLift_compl_adj_core_core]
    exact (SimpleGraph.compl_adj _ _ _).2
      ⟨fun h ↦ huv.ne (congrArg Switching.Vertex.core h),
        fun hred ↦
          (SimpleGraph.compl_adj _ _ _).1 huv |>.2
            ((old_adj_core_core data d e).2 hred)⟩
  ·
    rw [ab3ReplaceProjection_core, ab3ReplaceProjection_b0,
      specialLift_compl_adj_core_a]
    intro h
    apply hcp
    simpa [h] using hu
  ·
    rw [ab3ReplaceProjection_core,
      ab3ReplaceProjection_b_of_ne data p p hp0',
      specialLift_compl_adj_core_b]
    by_cases hEq : d = data.cert.c p
    · exact Or.inl hEq
    · exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨Ne.symm hEq, fun hred ↦
          (SimpleGraph.compl_adj _ _ _).1 huv |>.2
            ((old_adj_core_b_iff data d p).2 ⟨hEq, hred⟩)⟩)
  ·
    rw [ab3ReplaceProjection_b0, ab3ReplaceProjection_core,
      specialLift_compl_adj_a_core]
    intro h
    apply hcp
    simpa [h] using hv
  · exact False.elim
      ((extraAOldGraph data)ᶜ.loopless.irrefl _ huv)
  ·
    rw [ab3ReplaceProjection_b0,
      ab3ReplaceProjection_b_of_ne data p p hp0',
      specialLift_compl_adj_a_b]
  ·
    rw [ab3ReplaceProjection_b_of_ne data p p hp0,
      ab3ReplaceProjection_core, specialLift_compl_adj_b_core]
    by_cases hEq : e = data.cert.c p
    · exact Or.inl hEq
    · exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨Ne.symm hEq, fun hred ↦
          (SimpleGraph.compl_adj _ _ _).1 huv |>.2
            ((extraAOldGraph data).adj_symm
              ((old_adj_core_b_iff data e p).2 ⟨hEq, hred⟩))⟩)
  ·
    rw [ab3ReplaceProjection_b_of_ne data p p hp0,
      ab3ReplaceProjection_b0, specialLift_compl_adj_b_a]
  · exact False.elim
      ((extraAOldGraph data)ᶜ.loopless.irrefl _ huv)

private theorem ab3ReplaceProjection_adjoins_endpoints
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hA : ∀ q : Fin (k - 1), Switching.Vertex.a q ∉ K)
    (p : Fin (k - 1))
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K →
        q = c0Index data ∨ q = p)
    {u : Switching.Vertex V k s} (hu : u ∈ K) :
    (specialLift G data.cert.c)ᶜ.Adj
        (ab3ReplaceProjection data p u) (.core (i0 data)) ∧
      (specialLift G data.cert.c)ᶜ.Adj
        (ab3ReplaceProjection data p u) (.core (i2 data)) := by
  rcases ab3Replace_member_cases
      data hG hKsub hXZero hYZero hA p hB hu with
      ⟨d, rfl⟩ | rfl | ⟨hp0, rfl⟩
  ·
    have hd := core_ab3_spec data hG hKsub
      (⟨d, hu⟩ : CoreIn K)
    constructor
    · rw [ab3ReplaceProjection_core,
        specialLift_compl_adj_core_core]
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨hd.1, fun hred ↦ hd.2.1 (G.adj_symm hred)⟩
    · rw [ab3ReplaceProjection_core,
        specialLift_compl_adj_core_core]
      exact (SimpleGraph.compl_adj _ _ _).2
        ⟨hd.2.2.1, fun hred ↦ hd.2.2.2 (G.adj_symm hred)⟩
  ·
    constructor
    · rw [ab3ReplaceProjection_b0,
        specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i p (i0Index data)
    · rw [ab3ReplaceProjection_b0,
        specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i p (i2Index data)
  ·
    have hp := (b_ab3_spec data hG hKsub
      (⟨p, hu⟩ : BIn K)).resolve_left hp0
    constructor
    · rw [ab3ReplaceProjection_b_of_ne data p p hp0,
        specialLift_compl_adj_b_core]
      exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨data.cert.c_ne_i p (i0Index data), hp.2.1⟩)
    · rw [ab3ReplaceProjection_b_of_ne data p p hp0,
        specialLift_compl_adj_b_core]
      exact Or.inr ((SimpleGraph.compl_adj _ _ _).2
        ⟨data.cert.c_ne_i p (i2Index data), hp.2.2⟩)

private theorem card_ab3_no_xy_replace_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0)
    (hA : ∀ q : Fin (k - 1), Switching.Vertex.a q ∉ K)
    (p : Fin (k - 1))
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K →
        q = c0Index data ∨ q = p)
    (hcp : Switching.Vertex.core (data.cert.c p) ∉ K) :
    K.card ≤ s - 2 := by
  exact card_ab3_of_projection data hG hK
    (ab3ReplaceProjection data p)
    (fun {_ _} hu hv huv ↦
      ab3ReplaceProjection_maps_adj data hG hKsub
        hXZero hYZero hA p hB hcp hu hv huv)
    (fun {_} hu ↦
      ab3ReplaceProjection_adjoins_endpoints data hG hKsub
        hXZero hYZero hA p hB hu)

private theorem card_ab3_no_xy_le
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKsub : (K : Set (Switching.Vertex V k s)) ⊆
      (extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
    (hK : (extraAOldGraph data)ᶜ.IsClique K)
    (hXZero : Fintype.card (XIn data.cert K) = 0)
    (hYZero : Fintype.card (YIn data.cert K) = 0) :
    K.card ≤ s - 2 := by
  classical
  by_cases hb0 :
      Switching.Vertex.b (c0Index data) ∈ K
  · have hA : ∀ q : Fin (k - 1),
        Switching.Vertex.a q ∉ K :=
      ab3_no_a_of_b0 data hG hKsub hK hb0
    by_cases hOther :
        ∃ p : Fin (k - 1),
          p ≠ c0Index data ∧ Switching.Vertex.b p ∈ K
    · obtain ⟨p, hp0, hpK⟩ := hOther
      have hpLarge :
          2 ≤ p.val :=
        (b_ab3_zero_or_large data hG hKsub
          (⟨p, hpK⟩ : BIn K)).resolve_left hp0
      have hB : ∀ q : Fin (k - 1),
          Switching.Vertex.b q ∈ K →
            q = c0Index data ∨ q = p := by
        intro q hqK
        by_cases hq0 : q = c0Index data
        · exact Or.inl hq0
        · right
          by_contra hqp
          have hqLarge :
              2 ≤ q.val :=
            (b_ab3_zero_or_large data hG hKsub
              (⟨q, hqK⟩ : BIn K)).resolve_left hq0
          have hblue := hK hqK hpK (by
            intro h
            exact hqp (vertex_b_injective h))
          exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
            ((old_adj_b_b_iff data q p).2
              (Or.inl ⟨hqp,
                Or.inr ⟨hqLarge, hpLarge⟩⟩))
      have hcp :
          Switching.Vertex.core (data.cert.c p) ∉ K := by
        intro hcpK
        have hblue := hK hb0 hcpK (by simp)
        exact (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
          (old_adj_b0_cp_of_ne data p hp0)
      exact card_ab3_no_xy_replace_le data hG hKsub hK
        hXZero hYZero hA p hB hcp
    · have hB : ∀ q : Fin (k - 1),
          Switching.Vertex.b q ∈ K →
            q = c0Index data ∨ q = c0Index data := by
        intro q hqK
        by_cases hq0 : q = c0Index data
        · exact Or.inl hq0
        · exact False.elim (hOther ⟨q, hq0, hqK⟩)
      have hc0 :
          Switching.Vertex.core
            (data.cert.c (c0Index data)) ∉ K := by
        intro hc0K
        have hd := core_ab3_spec data hG hKsub
          (⟨data.cert.c (c0Index data), hc0K⟩ : CoreIn K)
        exact hd.2.1
          (G.adj_symm data.c0_i0_red)
      exact card_ab3_no_xy_replace_le data hG hKsub hK
        hXZero hYZero hA (c0Index data) hB hc0
  · exact card_ab3_no_xy_no_b0_le data hG hKsub hK
      hXZero hYZero hb0

/-- Row A-B3: the newly blue edge `y₀y₂` has no common blue
`K_(s-1)`.  The no-`X` branch explicitly retains or replaces `b₀`
according to whether a second `B`-vertex occurs. -/
theorem blue_common_y0_y2_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data)ᶜ.CliqueFreeOn
      ((extraAOldGraph data)ᶜ.commonNeighbors (y0 data) (y2 data))
      (s - 1) := by
  classical
  intro K hKsub hK
  have hcard := hK.card_eq
  by_cases hXlarge : 2 ≤ Fintype.card (XIn data.cert K)
  · have hle :=
      card_ab3_many_x_le data hG hKsub hK.isClique hXlarge
    have hs := data.cert.five_le_s
    omega
  · have hXle : Fintype.card (XIn data.cert K) ≤ 1 := by
      omega
    by_cases hXZero : Fintype.card (XIn data.cert K) = 0
    · by_cases hYZero : Fintype.card (YIn data.cert K) = 0
      · have hle :=
          card_ab3_no_xy_le data hG hKsub hK.isClique
            hXZero hYZero
        have hs := data.cert.five_le_s
        omega
      · have hYPos : 0 < Fintype.card (YIn data.cert K) := by
          omega
        have hle :=
          card_ab3_no_x_with_y_le data hG hKsub hK.isClique
            hXZero hYPos
        have hs := data.cert.five_le_s
        omega
    · have hXOne : Fintype.card (XIn data.cert K) = 1 := by
        omega
      have hle :=
        card_ab3_one_x_le data hG hKsub hK.isClique hXOne
      have hs := data.cert.five_le_s
      omega

private theorem extraAOldGraph_red_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data).CliqueFree (k + 1) := by
  classical
  have hk := data.cert.five_le_k
  have hsize : (k - 1) + 2 = k + 1 := by omega
  have hbase :=
    (Switching.switching_extension data.cert hG).1
  have hbase' :
      (Switching.finalGraph data.cert).CliqueFree
        ((k - 1) + 2) := by
    rw [hsize]
    exact hbase
  have hsafe :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        extraAAddedRedRel data u v →
          (extraAOldGraph data).CliqueFreeOn
            ((extraAOldGraph data).commonNeighbors u v)
            (k - 1) := by
    intro u v h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact red_common_i0_a2_cliqueFree data
    · rcases h with ⟨rfl, rfl⟩
      rw [SimpleGraph.commonNeighbors_symm]
      exact red_common_i0_a2_cliqueFree data
  have hclassify :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        (extraAOldGraph data).Adj u v →
          ¬(Switching.finalGraph data.cert).Adj u v →
            extraAAddedRedRel data u v := by
    intro u v hnew hold
    exact classify_extraA_new_red_edge data hnew hold
  have hresult :=
    Switching.cliqueFree_of_new_edges
      (G₀ := Switching.finalGraph data.cert)
      (G₁ := extraAOldGraph data)
      (n := k - 1)
      (Dangerous := extraAAddedRedRel data)
      hbase'
      hclassify
      hsafe
  rw [hsize] at hresult
  exact hresult

private theorem extraAOldGraph_blue_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data)ᶜ.CliqueFree (s + 1) := by
  classical
  have hs := data.cert.five_le_s
  have hsize : (s - 1) + 2 = s + 1 := by omega
  have hbase :=
    (Switching.switching_extension data.cert hG).2
  have hbase' :
      (Switching.finalGraph data.cert)ᶜ.CliqueFree
        ((s - 1) + 2) := by
    rw [hsize]
    exact hbase
  have hsafe :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        extraARemovedRedRel data u v →
          (extraAOldGraph data)ᶜ.CliqueFreeOn
            ((extraAOldGraph data)ᶜ.commonNeighbors u v)
            (s - 1) := by
    intro u v h
    rcases h with h | h | h
    · obtain ⟨p, hp, h | h⟩ := h
      · rcases h with ⟨rfl, rfl⟩
        exact blue_common_cp_xStar_cliqueFree data hG p hp
      · rcases h with ⟨rfl, rfl⟩
        rw [SimpleGraph.commonNeighbors_symm]
        exact blue_common_cp_xStar_cliqueFree data hG p hp
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact blue_common_y0_yStar_cliqueFree data hG
      · rcases h with ⟨rfl, rfl⟩
        rw [SimpleGraph.commonNeighbors_symm]
        exact blue_common_y0_yStar_cliqueFree data hG
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact blue_common_y0_y2_cliqueFree data hG
      · rcases h with ⟨rfl, rfl⟩
        rw [SimpleGraph.commonNeighbors_symm]
        exact blue_common_y0_y2_cliqueFree data hG
  have hclassify :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        (extraAOldGraph data)ᶜ.Adj u v →
          ¬(Switching.finalGraph data.cert)ᶜ.Adj u v →
            extraARemovedRedRel data u v := by
    intro u v hnew hold
    exact classify_extraA_new_blue_edge data hnew hold
  have hresult :=
    Switching.cliqueFree_of_new_edges
      (G₀ := (Switching.finalGraph data.cert)ᶜ)
      (G₁ := (extraAOldGraph data)ᶜ)
      (n := s - 1)
      (Dangerous := extraARemovedRedRel data)
      hbase'
      hclassify
      hsafe
  rw [hsize] at hresult
  exact hresult

/-- The four Type A switches preserve the old graph's
`(k+1,s+1)`-Ramsey freeness. -/
theorem extraAOldGraph_isRamseyFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (extraAOldGraph data) (k + 1) (s + 1) :=
  ⟨extraAOldGraph_red_cliqueFree data hG,
    extraAOldGraph_blue_cliqueFree data hG⟩

end TypeA
end SecondConnector
end RamseyIncrement
