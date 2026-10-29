/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.TypeB.OldEdges
import RamseyIncrement.SecondConnector.Projection

/-!
# Type B red cliques through the second connector

This file formalizes the Type B red-neighborhood analysis from the
strengthened second-connector argument.  The proof follows its three-way
split: a clique containing `y₂`, a clique containing `y_*`, and a clique
containing no `Y`-vertex.  In the `y₂` row the possible vertex `a₀` is
retained and handled by the direct
`1 + 1 + 1 + (k - 4)` count.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private abbrev c0
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.c (Certificates.c0Index data.cert.five_le_k)

private abbrev c2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.c (c2Index data)

private abbrev i2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.i (i2Index data)

private abbrev a0
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a
    (Certificates.c0Index data.cert.five_le_k)

private abbrev xStar
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

private abbrev y2
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert (some (i2Index data))

private abbrev yStar
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert none

private abbrev zVertex : Switching.Vertex V k s :=
  Switching.Vertex.z

private theorem c0_ne_c2
    (data : Certificates.PlusCaseBData G k s) :
    Certificates.c0Index data.cert.five_le_k ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c2Index, Certificates.c0Index] at hval

private theorem card_index_away_from_two
    (data : Certificates.PlusCaseBData G k s) :
    Fintype.card
      {p : Fin (k - 1) // p ≠ c2Index data} = k - 2 := by
  classical
  have hone :
      Fintype.card
        {p : Fin (k - 1) // p = c2Index data} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨c2Index data, rfl⟩, by
      rintro ⟨p, hp⟩
      exact Subtype.ext hp⟩
  rw [Fintype.card_subtype_compl
    (fun p : Fin (k - 1) => p = c2Index data)]
  simp only [Fintype.card_fin, hone]
  have hk := data.cert.five_le_k
  omega

private theorem card_index_away_from_zero_two
    (data : Certificates.PlusCaseBData G k s) :
    Fintype.card
      {p : Fin (k - 1) //
        ¬(p = Certificates.c0Index data.cert.five_le_k ∨
          p = c2Index data)} = k - 3 := by
  classical
  let e :
      {p : Fin (k - 1) //
        p = Certificates.c0Index data.cert.five_le_k ∨
          p = c2Index data} ≃ Bool :=
    { toFun := fun p =>
        if p.1 = Certificates.c0Index data.cert.five_le_k
          then false else true
      invFun := fun b =>
        if b then
          ⟨c2Index data, Or.inr rfl⟩
        else
          ⟨Certificates.c0Index data.cert.five_le_k,
            Or.inl rfl⟩
      left_inv := by
        rintro ⟨p, hp⟩
        apply Subtype.ext
        rcases hp with hp | hp
        · subst p
          simp
        · subst p
          simp [(c0_ne_c2 data).symm]
      right_inv := by
        intro b
        cases b <;> simp [(c0_ne_c2 data).symm] }
  have htwo :
      Fintype.card
        {p : Fin (k - 1) //
          p = Certificates.c0Index data.cert.five_le_k ∨
            p = c2Index data} = 2 := by
    calc
      _ = Fintype.card Bool := Fintype.card_congr e
      _ = 2 := Fintype.card_bool
  rw [Fintype.card_subtype_compl
    (fun p : Fin (k - 1) =>
      p = Certificates.c0Index data.cert.five_le_k ∨
        p = c2Index data)]
  simp only [Fintype.card_fin, htwo]
  have hk := data.cert.five_le_k
  omega

/-! ## Neighborhood and source-graph facts -/

/-- The block form of the red neighborhood in (19B). -/
private theorem red_member_cases
    (data : Certificates.PlusCaseBData G k s)
    {v : Switching.Vertex V k s}
    (hv : redToWB data v) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ((∃ p, d = data.cert.c p) ∨ G.Adj (i2 data) d)) ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.a p ∧ p ≠ c2Index data) ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.b p ∧ 3 ≤ p.val) ∨
    v = xStar data ∨
    v = y2 data ∨
    v = yStar data ∨
    v = zVertex := by
  rcases vertex_six_block_cases data.cert v with
      h | h | h | h | h | h
  · obtain ⟨d, rfl⟩ := h
    exact Or.inl ⟨d, rfl, (redToWB_core data d).1 hv⟩
  · obtain ⟨p, rfl⟩ := h
    exact Or.inr (Or.inl
      ⟨p, rfl, (redToWB_a data p).1 hv⟩)
  · obtain ⟨p, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl
      ⟨p, rfl, (redToWB_b data p).1 hv⟩))
  · obtain ⟨r, rfl⟩ := h
    have hr := (redToWB_x data r).1 hv
    subst r
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · obtain ⟨r, rfl⟩ := h
    rcases (redToWB_y data r).1 hv with hr | hr
    · subst r
      exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl)))))
    · subst r
      exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl))))
  · subst v
    exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr rfl)))))

/-- The only new red old-graph edge meets `a₂`, which is not red to
`w`; hence clique edges inside `N_R(w)` already occur in `finalGraph`. -/
private theorem old_adj_implies_final
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (hu : redToWB data u) (hv : redToWB data v)
    (huv : (extraBOldGraph data).Adj u v) :
    (Switching.finalGraph data.cert).Adj u v := by
  by_contra hfinal
  have hnew := classify_extraB_new_red_edge data huv hfinal
  rcases hnew with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ((redToWB_a data (c2Index data)).1 hv) rfl
  · rcases h with ⟨rfl, rfl⟩
    exact ((redToWB_a data (c2Index data)).1 hu) rfl

private theorem final_adj_core_core_iff
    (data : Certificates.PlusCaseBData G k s) (u v : V) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core u) (Switching.Vertex.core v) ↔
        G.Adj u v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_core]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_core_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.a p) ↔
        data.cert.c p = v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_core_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.b p) ↔
        v ≠ data.cert.c p ∧ G.Adj (data.cert.c p) v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_adj_core_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (q : Fin (s - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v)
      (Switching.Vertex.y data.cert (some q)) ↔
        v = data.cert.i q ∨ G.Adj (data.cert.i q) v := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_adj_core_yStar_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (yStar data) ↔
        v = c0 data := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, eq_comm]

private theorem final_adj_b_y_iff_of_ne_c0
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1))
    (hp0 : p ≠ Certificates.c0Index data.cert.five_le_k) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.b p)
      (Switching.Vertex.y data.cert (some q)) ↔
        G.Adj (data.cert.c p) (data.cert.i q) := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, hp0]
  intro _ hEq
  exact data.cert.c_ne_i p q hEq.symm

private theorem final_adj_z_core_iff
    (data : Certificates.PlusCaseBData G k s) (v : V) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.core v) ↔
        v ≠ c0 data ∧ G.Adj (c0 data) v := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core, Switching.Vertex.b, zVertex, c0]

private theorem final_adj_z_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.b p) ↔
        p = Certificates.c0Index data.cert.five_le_k ∨
          (Certificates.c0Index data.cert.five_le_k ≠ p ∧
            SameBPart
              (Certificates.c0Index data.cert.five_le_k) p) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.b, zVertex]
  aesop

private theorem final_adj_z_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.y data.cert (some q)) ↔
        q ∈ data.cert.T := by
  have hpre :
      (Switching.preGraph data.cert).Adj zVertex
          (Switching.Vertex.y data.cert (some q)) ↔
        q ∈ data.cert.T := by
    change
      (Switching.redJoinedClone (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.b ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              data.cert.five_le_s)).symm (some q)))) ↔
        q ∈ data.cert.T
    rw [Switching.redJoinedClone.adj_z_old]
    rw [or_iff_right (by simp)]
    exact Switching.preGraph_adj_b0_y_iff data.cert q
  rw [Switching.final_adj_iff, hpre]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_not_adj_y_a_of_ne_c0
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1))
    (hp0 : p ≠ Certificates.c0Index data.cert.five_le_k) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.y data.cert (some q))
      (Switching.Vertex.a p) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, hp0]
  exact data.cert.c_ne_i p q

private theorem final_not_adj_ySome_xStar
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.y data.cert (some q)) (xStar data) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, xStar]

private theorem final_not_adj_z_a0
    (data : Certificates.PlusCaseBData G k s) :
    ¬(Switching.finalGraph data.cert).Adj zVertex (a0 data) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b, zVertex, a0]

private theorem final_not_adj_y2_yStar
    (data : Certificates.PlusCaseBData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (y2 data) (yStar data) := by
  have hs : 2 < s := by
    have := data.cert.five_le_s
    omega
  have hpre :
      ¬(Switching.preGraph data.cert).Adj
        (y2 data) (yStar data) := by
    rw [Switching.preGraph_adj_y_y_iff]
    simp [Canonical.outerIndexEquiv, SameBPart,
      i2Index]
    omega
  rw [Switching.final_adj_iff]
  simp [hpre, Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, y2, yStar]

private theorem final_not_adj_z_yStar
    (data : Certificates.PlusCaseBData G k s) :
    ¬(Switching.finalGraph data.cert).Adj zVertex (yStar data) := by
  have hpre :
      ¬(Switching.preGraph data.cert).Adj
        zVertex (yStar data) := by
    change
      ¬(Switching.redJoinedClone
        (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.b ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              data.cert.five_le_s)).symm none)))
    rw [Switching.redJoinedClone.adj_z_old]
    push Not
    constructor
    · simp
    · exact Switching.preGraph_not_adj_b0_yStar data.cert
  rw [Switching.final_adj_iff]
  simp [hpre, Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, yStar]

private theorem final_not_adj_a_b_same
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.b p) := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b]

private theorem final_not_adj_xStar_a0
    (data : Certificates.PlusCaseBData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (xStar data) (a0 data) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, xStar, a0]

private theorem final_adj_a_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (p q : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.a q) ↔
        p ≠ q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_a_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p q : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.b q) ↔
        p ≠ q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_b_b_iff_of_large
    (data : Certificates.PlusCaseBData G k s)
    (p q : Fin (k - 1))
    (hp : 3 ≤ p.val) (hq : 3 ≤ q.val) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.b p) (Switching.Vertex.b q) ↔
        p ≠ q ∧ SameBPart p q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_b_b]
  have hp0 :
      p ≠ Certificates.c0Index data.cert.five_le_k := by
    intro h
    have hval := congrArg Fin.val h
    simp [Certificates.c0Index] at hval
    omega
  have hp2 : p ≠ c2Index data := by
    intro h
    have hval := congrArg Fin.val h
    simp [c2Index, Certificates.c2Index] at hval
    omega
  have hq0 :
      q ≠ Certificates.c0Index data.cert.five_le_k := by
    intro h
    have hval := congrArg Fin.val h
    simp [Certificates.c0Index] at hval
    omega
  have hq2 : q ≠ c2Index data := by
    intro h
    have hval := congrArg Fin.val h
    simp [c2Index, Certificates.c2Index] at hval
    omega
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, hp0, hp2, hq0, hq2]

private theorem final_adj_z_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.a p) ↔
        p ≠ Certificates.c0Index data.cert.five_le_k := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b, zVertex]

private theorem extraBOldGraph_not_adj_c2_xStar
    (data : Certificates.PlusCaseBData G k s) :
    ¬(extraBOldGraph data).Adj
      (Switching.Vertex.core (c2 data)) (xStar data) := by
  apply extraBOldGraph_not_adj_of_removed data
  rw [extraBRemovedRedGraph_adj_iff]
  exact Or.inl ⟨rfl, rfl⟩

private theorem c0_adj_i2
    (data : Certificates.PlusCaseBData G k s) :
    G.Adj (c0 data) (i2 data) := by
  have h :=
    data.cert.caseB_adj_of_ne data.baseB (c0_ne_c2 data)
  rw [Certificates.castIndex_c2'
    data.cert.five_le_k data.cert.five_le_s
    data.baseB.k_le_s] at h
  exact h

private theorem not_old_adj_z_b_of_large
    (data : Certificates.PlusCaseBData G k s)
    {p : Fin (k - 1)} (hp : 3 ≤ p.val) :
    ¬(extraBOldGraph data).Adj zVertex
      (Switching.Vertex.b p) := by
  intro h
  have hf := old_adj_implies_final data
    (redToWB_z data) ((redToWB_b data p).2 hp) h
  rcases (final_adj_z_b_iff data p).1 hf with hp0 | hp0
  · have hval := congrArg Fin.val hp0
    simp [Certificates.c0Index] at hval
    omega
  · rcases hp0.2 with hsmall | hlarge
    · omega
    · have h0 := hlarge.1
      simp [Certificates.c0Index] at h0

private theorem cert_i_not_red
    (data : Certificates.PlusCaseBData G k s)
    (q r : Fin (s - 1)) :
    ¬G.Adj (data.cert.i q) (data.cert.i r) := by
  by_cases hqr : q = r
  · subst r
    exact G.loopless.irrefl _
  · exact ((SimpleGraph.compl_adj _ _ _).1
      (data.cert.i_compl_adj hqr)).2

private theorem not_redToWB_core_i2
    (data : Certificates.PlusCaseBData G k s) :
    ¬redToWB data (Switching.Vertex.core (i2 data)) := by
  rw [redToWB_core]
  rintro (⟨p, hp⟩ | hred)
  · exact data.cert.c_ne_i p (i2Index data) hp.symm
  · exact cert_i_not_red data (i2Index data) (i2Index data) hred

/-! ## The `y₂` projection and direct-count rows -/

private theorem member_cases_y2_no_a0
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K)
    (ha0 : a0 data ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), 3 ≤ p.val ∧
      v = Switching.Vertex.b p) ∨
    v = y2 data ∨
    v = zVertex := by
  have hvred : redToWB data v := hKS hv
  have hyred : redToWB data (y2 data) := hKS hy2
  rcases red_member_cases data hvred with
      hcore | ha | hb | hx | hy2' | hys | hz
  · obtain ⟨d, hd, _⟩ := hcore
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨p, rfl, _⟩ := ha
    by_cases hp0 :
        p = Certificates.c0Index data.cert.five_le_k
    · subst p
      exact False.elim (ha0 hv)
    · have hfinal := old_adj_implies_final data hyred hvred
        (hK hy2 hv (by simp))
      exact False.elim
        (final_not_adj_y_a_of_ne_c0 data (i2Index data) p hp0 hfinal)
  · obtain ⟨p, rfl, hp⟩ := hb
    exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
  · subst v
    have hfinal := old_adj_implies_final data hyred hvred
      (hK hy2 hv (by simp [xStar, y2]))
    exact False.elim
      (final_not_adj_ySome_xStar data (i2Index data) hfinal)
  · exact Or.inr (Or.inr (Or.inl hy2'))
  · subst v
    have hfinal := old_adj_implies_final data hyred hvred
      (hK hy2 hv (by simp [y2, yStar]))
    exact False.elim (final_not_adj_y2_yStar data hfinal)
  · exact Or.inr (Or.inr (Or.inr hz))

private def y2Projection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → V
  | .inl (.core (.core v)) => v
  | .inl (.core (.b p)) => data.cert.c p
  | .inl (.b _) => i2 data
  | .inr _ => c0 data
  | _ => c0 data

@[simp]
private theorem y2Projection_core
    (data : Certificates.PlusCaseBData G k s) (v : V) :
    y2Projection data (Switching.Vertex.core v) = v :=
  rfl

@[simp]
private theorem y2Projection_b
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    y2Projection data (Switching.Vertex.b p) = data.cert.c p :=
  rfl

@[simp]
private theorem y2Projection_y2
    (data : Certificates.PlusCaseBData G k s) :
    y2Projection data (y2 data) = i2 data := by
  simp [y2Projection]

@[simp]
private theorem y2Projection_z
    (data : Certificates.PlusCaseBData G k s) :
    y2Projection data zVertex = c0 data :=
  rfl

private theorem y2Projection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K)
    (ha0 : a0 data ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraBOldGraph data).Adj u v) :
    G.Adj (y2Projection data u) (y2Projection data v) := by
  have hured := hKS hu
  have hvred := hKS hv
  have hufinal := old_adj_implies_final data hured hvred huv
  rcases member_cases_y2_no_a0 data hKS hK hy2 ha0 hu with
      ⟨d, rfl⟩ | ⟨p, hp, rfl⟩ | rfl | rfl <;>
    rcases member_cases_y2_no_a0 data hKS hK hy2 ha0 hv with
      ⟨e, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl
  · simpa using (final_adj_core_core_iff data d e).1 hufinal
  · simpa using ((final_adj_core_b_iff data d r).1 hufinal).2.symm
  · rcases (final_adj_core_y_iff data d (i2Index data)).1
      hufinal with h | h
    · subst d
      exact False.elim (not_redToWB_core_i2 data hured)
    · simpa using h.symm
  · simpa using ((final_adj_z_core_iff data d).1
      ((Switching.finalGraph data.cert).adj_symm hufinal)).2.symm
  · simpa using ((final_adj_core_b_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hufinal)).2
  · simpa using data.cert.c_adj
      (fun hpr ↦ huv.ne (congrArg Switching.Vertex.b hpr))
  · have hp0 :
        p ≠ Certificates.c0Index data.cert.five_le_k := by
      intro hp0
      subst p
      simp [Certificates.c0Index] at hp
    simpa using (final_adj_b_y_iff_of_ne_c0 data p
      (i2Index data) hp0).1 hufinal
  · exact False.elim
      (not_old_adj_z_b_of_large data hp
        ((extraBOldGraph data).adj_symm huv))
  · rcases (final_adj_core_y_iff data e (i2Index data)).1
      ((Switching.finalGraph data.cert).adj_symm hufinal) with h | h
    · subst e
      exact False.elim (not_redToWB_core_i2 data hvred)
    · simpa using h
  · have hr0 :
        r ≠ Certificates.c0Index data.cert.five_le_k := by
      intro hr0
      subst r
      simp [Certificates.c0Index] at hr
    simpa using ((final_adj_b_y_iff_of_ne_c0 data r
      (i2Index data) hr0).1
        ((Switching.finalGraph data.cert).adj_symm hufinal)).symm
  · exact False.elim (huv.ne rfl)
  · have hT := (final_adj_z_y_iff data (i2Index data)).1
      ((Switching.finalGraph data.cert).adj_symm hufinal)
    simpa using ((data.cert.mem_T (i2Index data)).1 hT).symm
  · simpa using ((final_adj_z_core_iff data e).1 hufinal).2
  · exact False.elim (not_old_adj_z_b_of_large data hr huv)
  · have hT := (final_adj_z_y_iff data (i2Index data)).1 hufinal
    simpa using (data.cert.mem_T (i2Index data)).1 hT
  · exact False.elim (huv.ne rfl)

private theorem card_lt_of_y2_no_a0
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K)
    (ha0 : a0 data ∉ K) :
    K.card < k := by
  let f := y2Projection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraBOldGraph data).Adj u v → G.Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      y2Projection_maps_adj data hKS hK hy2 ha0 hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hG.1.cliqueFreeOn hK

private theorem card_largeB_le
    (_data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hlarge : ∀ p : BIn K, 3 ≤ p.1.val) :
    Fintype.card (BIn K) ≤ k - 4 := by
  classical
  let f : BIn K ↪ Fin (k - 4) :=
    { toFun := fun p ↦
        ⟨p.1.val - 3, by
          have hlt := p.1.isLt
          have hp := hlarge p
          omega⟩
      inj' := by
        intro p q hpq
        apply Subtype.ext
        apply Fin.ext
        have hval := congrArg Fin.val hpq
        dsimp at hval
        have hp := hlarge p
        have hq := hlarge q
        omega }
  simpa using Fintype.card_le_of_injective f f.injective

private theorem card_lt_of_y2_with_a0
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K)
    (ha0 : a0 data ∈ K) :
    K.card < k := by
  classical
  have hyred : redToWB data (y2 data) := hKS hy2
  have ha0red : redToWB data (a0 data) := hKS ha0
  have hCoreOne : Fintype.card (CoreIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro d e
    apply Subtype.ext
    have hdFinal := old_adj_implies_final data ha0red (hKS d.2)
      (hK ha0 d.2 (by simp))
    have heFinal := old_adj_implies_final data ha0red (hKS e.2)
      (hK ha0 e.2 (by simp))
    have hd : d.1 = c0 data := by
      exact (final_adj_core_a_iff data d.1
        (Certificates.c0Index data.cert.five_le_k)).1
          ((Switching.finalGraph data.cert).adj_symm hdFinal) |>.symm
    have he : e.1 = c0 data := by
      exact (final_adj_core_a_iff data e.1
        (Certificates.c0Index data.cert.five_le_k)).1
          ((Switching.finalGraph data.cert).adj_symm heFinal) |>.symm
    exact hd.trans he.symm
  have hAOne : Fintype.card (AIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    have hp : p.1 =
        Certificates.c0Index data.cert.five_le_k := by
      by_contra hp0
      exact final_not_adj_y_a_of_ne_c0 data (i2Index data) p.1 hp0
        (old_adj_implies_final data hyred (hKS p.2)
          (hK hy2 p.2 (by simp)))
    have hq : q.1 =
        Certificates.c0Index data.cert.five_le_k := by
      by_contra hq0
      exact final_not_adj_y_a_of_ne_c0 data (i2Index data) q.1 hq0
        (old_adj_implies_final data hyred (hKS q.2)
          (hK hy2 q.2 (by simp)))
    exact hp.trans hq.symm
  have hBlarge : ∀ p : BIn K, 3 ≤ p.1.val := by
    intro p
    rcases red_member_cases data (hKS p.2) with
        h | h | h | h | h | h | h
    · obtain ⟨d, heq, _⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨q, heq, _⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨q, heq, hq⟩ := h
      have hpq : p.1 = q := vertex_b_injective heq
      simpa [hpq] using hq
    · have := congrArg blockTag h
      simp at this
    · have := congrArg blockTag h
      simp at this
    · have := congrArg blockTag h
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hBle := card_largeB_le data hBlarge
  have hXZero : Fintype.card (XIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro x
    have hxred : redToWB data
        (Switching.Vertex.x data.cert x.1) := hKS x.2
    rcases red_member_cases data hxred with
        h | h | h | h | h | h | h
    · obtain ⟨d, heq, _⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨p, heq, _⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨p, heq, _⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have hx : Switching.Vertex.x data.cert x.1 = xStar data := h
      have hfinal := old_adj_implies_final data hyred hxred
        (hK hy2 x.2 (by simp))
      exact final_not_adj_ySome_xStar data (i2Index data)
        (hx ▸ hfinal)
    · have := congrArg blockTag h
      simp at this
    · have := congrArg blockTag h
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hYIndex :
      ∀ r : YIn data.cert K, r.1 = some (i2Index data) := by
    intro r
    have hrred : redToWB data
        (Switching.Vertex.y data.cert r.1) := hKS r.2
    rcases (redToWB_y data r.1).1 hrred with hr | hr
    · have hfinal := old_adj_implies_final data hyred hrred
        (hK hy2 r.2 (by
          intro heq
          have hindex := vertex_y_injective data.cert heq
          simp [hr] at hindex))
      rw [hr] at hfinal
      exact False.elim (final_not_adj_y2_yStar data hfinal)
    · exact hr
  have hYOne : Fintype.card (YIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    exact (hYIndex r).trans (hYIndex t).symm
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro z
    have hzred : redToWB data zVertex := by
      exact hKS z.2
    have hzFinal := old_adj_implies_final data ha0red hzred
      (hK ha0 z.2 (by simp))
    exact final_not_adj_z_a0 data
      ((Switching.finalGraph data.cert).adj_symm hzFinal)
  have hparts := card_eq_six_blocks data.cert K
  have hk := data.cert.five_le_k
  omega

theorem red_clique_card_lt_of_y2
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K) :
    K.card < k := by
  by_cases ha0 : a0 data ∈ K
  · exact card_lt_of_y2_with_a0 data hKS hK hy2 ha0
  · exact card_lt_of_y2_no_a0 data hG hKS hK hy2 ha0

/-! ## The `y_*` counting row -/

private theorem core_eq_c0_of_mem_yStar_clique
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K)
    {d : V} (hd : Switching.Vertex.core d ∈ K) :
    d = c0 data := by
  have hyred : redToWB data (yStar data) := hKS hyStar
  have hdred : redToWB data (Switching.Vertex.core d) := hKS hd
  have hfinal := old_adj_implies_final data hyred hdred
    (hK hyStar hd (by simp [yStar]))
  exact (final_adj_core_yStar_iff data d).1
    ((Switching.finalGraph data.cert).adj_symm hfinal)

private theorem z_not_mem_of_mem_yStar_clique
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K) :
    zVertex ∉ K := by
  intro hz
  have hyred : redToWB data (yStar data) := hKS hyStar
  have hzred : redToWB data zVertex := hKS hz
  have hfinal := old_adj_implies_final data hyred hzred
    (hK hyStar hz (by simp [yStar, zVertex]))
  exact final_not_adj_z_yStar data
    ((Switching.finalGraph data.cert).adj_symm hfinal)

private theorem y_index_eq_none_of_mem_yStar_clique
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K)
    {r : Option (Fin (s - 1))}
    (hr : Switching.Vertex.y data.cert r ∈ K) :
    r = none := by
  have hrred : redToWB data
      (Switching.Vertex.y data.cert r) := hKS hr
  rcases (redToWB_y data r).1 hrred with h | h
  · exact h
  · subst r
    have hfinal := old_adj_implies_final data hrred (hKS hyStar)
      (hK hr hyStar (by simp [yStar]))
    exact False.elim (final_not_adj_y2_yStar data hfinal)

private theorem x_index_eq_none_of_mem_red_neighborhood
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    {r : Option (Fin (s - 1))}
    (hr : Switching.Vertex.x data.cert r ∈ K) :
    r = none :=
  (redToWB_x data r).1 (hKS hr)

private theorem a_index_eq_c0_of_core_c0
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hc0 : Switching.Vertex.core (c0 data) ∈ K)
    {p : Fin (k - 1)}
    (hp : Switching.Vertex.a p ∈ K) :
    p = Certificates.c0Index data.cert.five_le_k := by
  have hfinal := old_adj_implies_final data (hKS hc0) (hKS hp)
    (hK hc0 hp (by simp))
  exact data.cert.c.injective
    ((final_adj_core_a_iff data (c0 data) p).1 hfinal)

private theorem a0_not_mem_of_xStar
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hx : xStar data ∈ K) :
    a0 data ∉ K := by
  intro ha0
  have hfinal := old_adj_implies_final data (hKS hx) (hKS ha0)
    (hK hx ha0 (by simp [xStar, a0]))
  exact final_not_adj_xStar_a0 data hfinal

private theorem not_both_matched
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (p : Fin (k - 1))
    (ha : Switching.Vertex.a p ∈ K)
    (hb : Switching.Vertex.b p ∈ K) :
    False := by
  have hfinal := old_adj_implies_final data (hKS ha) (hKS hb)
    (hK ha hb (by simp))
  exact final_not_adj_a_b_same data p hfinal

private theorem card_aIn_add_card_bIn_le_sub_two
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K) :
    Fintype.card (AIn K) + Fintype.card (BIn K) ≤ k - 2 := by
  classical
  let f :
      (AIn K ⊕ BIn K) ↪
        {p : Fin (k - 1) // p ≠ c2Index data} :=
    { toFun
        | Sum.inl p =>
            ⟨p.1, (redToWB_a data p.1).1 (hKS p.2)⟩
        | Sum.inr p =>
            ⟨p.1, by
              intro hp2
              have hpLarge :=
                (redToWB_b data p.1).1 (hKS p.2)
              have hval := congrArg Fin.val hp2
              simp [c2Index, Certificates.c2Index] at hval
              omega⟩
      inj' := by
        intro x y hxy
        rcases x with p | p <;> rcases y with q | q
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inl (Subtype.ext hpq)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqb : Switching.Vertex.b p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 p.2 hqb)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqa : Switching.Vertex.a p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 hqa p.2)
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inr (Subtype.ext hpq) }
  have hcard := Fintype.card_le_of_injective f f.injective
  rw [Fintype.card_sum, card_index_away_from_two data] at hcard
  exact hcard

private theorem card_aIn_add_card_bIn_le_sub_three
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (ha0 : a0 data ∉ K) :
    Fintype.card (AIn K) + Fintype.card (BIn K) ≤ k - 3 := by
  classical
  let f :
      (AIn K ⊕ BIn K) ↪
        {p : Fin (k - 1) //
          ¬(p = Certificates.c0Index data.cert.five_le_k ∨
            p = c2Index data)} :=
    { toFun
        | Sum.inl p =>
            ⟨p.1, by
              rintro (hp0 | hp2)
              · exact ha0 (by simpa [a0, hp0] using p.2)
              · exact (redToWB_a data p.1).1 (hKS p.2) hp2⟩
        | Sum.inr p =>
            ⟨p.1, by
              intro hp
              have hpLarge :=
                (redToWB_b data p.1).1 (hKS p.2)
              rcases hp with hp0 | hp2
              · have hval := congrArg Fin.val hp0
                simp [Certificates.c0Index] at hval
                omega
              · have hval := congrArg Fin.val hp2
                simp [c2Index, Certificates.c2Index] at hval
                omega⟩
      inj' := by
        intro x y hxy
        rcases x with p | p <;> rcases y with q | q
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inl (Subtype.ext hpq)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqb : Switching.Vertex.b p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 p.2 hqb)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqa : Switching.Vertex.a p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 hqa p.2)
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inr (Subtype.ext hpq) }
  have hcard := Fintype.card_le_of_injective f f.injective
  rw [Fintype.card_sum,
    card_index_away_from_zero_two data] at hcard
  exact hcard

/-- The `y_*` row, proved by four explicit block-index counts. -/
theorem red_clique_card_lt_of_yStar
    (data : Certificates.PlusCaseBData G k s)
    (_hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K) :
    K.card < k := by
  classical
  have hCoreLe : Fintype.card (CoreIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    calc
      p.1 = c0 data :=
        core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar p.2
      _ = q.1 :=
        (core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar q.2).symm
  have hXLe : Fintype.card (XIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    calc
      r.1 = none :=
        x_index_eq_none_of_mem_red_neighborhood data hKS r.2
      _ = t.1 :=
        (x_index_eq_none_of_mem_red_neighborhood
          data hKS t.2).symm
  have hYLe : Fintype.card (YIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    calc
      r.1 = none :=
        y_index_eq_none_of_mem_yStar_clique
          data hKS hK hyStar r.2
      _ = t.1 :=
        (y_index_eq_none_of_mem_yStar_clique
          data hKS hK hyStar t.2).symm
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro z
    exact z_not_mem_of_mem_yStar_clique
      data hKS hK hyStar (by simpa using z.2)
  have hBlarge : ∀ p : BIn K, 3 ≤ p.1.val := by
    intro p
    exact (redToWB_b data p.1).1 (hKS p.2)
  have hBLe := card_largeB_le data hBlarge
  have hparts := card_eq_six_blocks data.cert K
  have hk := data.cert.five_le_k
  by_cases hc0 : Switching.Vertex.core (c0 data) ∈ K
  · have hALe : Fintype.card (AIn K) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro p q
      apply Subtype.ext
      calc
        p.1 = Certificates.c0Index data.cert.five_le_k :=
          a_index_eq_c0_of_core_c0 data hKS hK hc0 p.2
        _ = q.1 :=
          (a_index_eq_c0_of_core_c0
            data hKS hK hc0 q.2).symm
    by_cases hx : xStar data ∈ K
    · have hAZero : Fintype.card (AIn K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro p
        have hp0 :=
          a_index_eq_c0_of_core_c0 data hKS hK hc0 p.2
        exact a0_not_mem_of_xStar data hKS hK hx
          (by simpa [a0, hp0] using p.2)
      omega
    · have hXZero :
          Fintype.card (XIn data.cert K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro r
        have hr :=
          x_index_eq_none_of_mem_red_neighborhood data hKS r.2
        exact hx (by simpa [xStar, hr] using r.2)
      omega
  · have hCoreZero : Fintype.card (CoreIn K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro d
      have hd :=
        core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar d.2
      exact hc0 (by simpa [hd] using d.2)
    by_cases hx : xStar data ∈ K
    · have ha0 := a0_not_mem_of_xStar data hKS hK hx
      have hAB :=
        card_aIn_add_card_bIn_le_sub_three
          data hKS hK ha0
      omega
    · have hXZero :
          Fintype.card (XIn data.cert K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro r
        have hr :=
          x_index_eq_none_of_mem_red_neighborhood data hKS r.2
        exact hx (by simpa [xStar, hr] using r.2)
      have hAB :=
        card_aIn_add_card_bIn_le_sub_two data hKS hK
      omega

/-! ## Cliques with no `Y`-vertex -/

private theorem member_cases_lower
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hnoZ : zVertex ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), v = Switching.Vertex.a p) ∨
    (∃ p : Fin (k - 1), 3 ≤ p.val ∧
      v = Switching.Vertex.b p) := by
  rcases red_member_cases data (hKS hv) with
      h | h | h | h | h | h | h
  · obtain ⟨d, heq, _⟩ := h
    exact Or.inl ⟨d, heq⟩
  · obtain ⟨p, heq, _⟩ := h
    exact Or.inr (Or.inl ⟨p, heq⟩)
  · obtain ⟨p, heq, hp⟩ := h
    exact Or.inr (Or.inr ⟨p, hp, heq⟩)
  · exact False.elim (hnoX (h ▸ hv))
  · exact False.elim (hnoY (some (i2Index data))
      (by simpa [h] using hv))
  · exact False.elim (hnoY none (by simpa [h] using hv))
  · exact False.elim (hnoZ (h ▸ hv))

private def lowerProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core d) => d
  | _ => .a (Certificates.c0Index data.cert.five_le_k)

@[simp]
private theorem lowerProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    lowerProjection data (Switching.Vertex.core d) =
      SpecialLiftVertex.core d :=
  rfl

@[simp]
private theorem lowerProjection_a
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    lowerProjection data (Switching.Vertex.a p) =
      SpecialLiftVertex.a p :=
  rfl

@[simp]
private theorem lowerProjection_b
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    lowerProjection data (Switching.Vertex.b p) =
      SpecialLiftVertex.b p :=
  rfl

private theorem lowerProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (_hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hnoZ : zVertex ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraBOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (lowerProjection data u) (lowerProjection data v) := by
  have hfinal := old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_lower data hKS hnoY hnoX hnoZ hu with
      ⟨d, rfl⟩ | ⟨p, rfl⟩ | ⟨p, hp, rfl⟩ <;>
    rcases member_cases_lower data hKS hnoY hnoX hnoZ hv with
      ⟨e, rfl⟩ | ⟨q, rfl⟩ | ⟨q, hq, rfl⟩
  all_goals
    simp only [lowerProjection_core, lowerProjection_a,
      lowerProjection_b]
  · rw [specialLift_adj_core_core]
    exact (final_adj_core_core_iff data d e).1 hfinal
  · rw [specialLift_adj_core_a]
    exact (final_adj_core_a_iff data d q).1 hfinal
  · rw [specialLift_adj_core_b]
    exact (final_adj_core_b_iff data d q).1 hfinal
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_a]
    exact (final_adj_core_a_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [specialLift_adj_a_a]
    exact (final_adj_a_a_iff data p q).1 hfinal
  · rw [specialLift_adj_a_b]
    exact (final_adj_a_b_iff data p q).1 hfinal
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_b]
    exact (final_adj_core_b_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_a_b]
    exact (final_adj_a_b_iff data q p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [specialLift_adj_b_b]
    exact (final_adj_b_b_iff_of_large data p q hp hq).1 hfinal

private theorem card_lt_of_lower_projection
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hnoZ : zVertex ∉ K) :
    K.card < k := by
  let f := lowerProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraBOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      lowerProjection_maps_adj data hKS hK
        hnoY hnoX hnoZ hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hfirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hfirst.1.cliqueFreeOn hK

private theorem member_cases_z_only
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hz : zVertex ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), v = Switching.Vertex.a p) ∨
    v = zVertex := by
  rcases red_member_cases data (hKS hv) with
      h | h | h | h | h | h | h
  · obtain ⟨d, heq, _⟩ := h
    exact Or.inl ⟨d, heq⟩
  · obtain ⟨p, heq, _⟩ := h
    exact Or.inr (Or.inl ⟨p, heq⟩)
  · obtain ⟨p, heq, hp⟩ := h
    have hb : Switching.Vertex.b p ∈ K := by
      simpa [heq] using hv
    exact False.elim (not_old_adj_z_b_of_large data hp
      (hK hz hb (by simp [zVertex])))
  · exact False.elim (hnoX (h ▸ hv))
  · exact False.elim (hnoY (some (i2Index data))
      (by simpa [h] using hv))
  · exact False.elim (hnoY none (by simpa [h] using hv))
  · exact Or.inr (Or.inr h)

private def zProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core d) => d
  | .inr _ =>
      .b (Certificates.c0Index data.cert.five_le_k)
  | _ => .core (c0 data)

@[simp]
private theorem zProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    zProjection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem zProjection_a
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    zProjection data (Switching.Vertex.a p) = .a p :=
  rfl

@[simp]
private theorem zProjection_z
    (data : Certificates.PlusCaseBData G k s) :
    zProjection data zVertex =
      .b (Certificates.c0Index data.cert.five_le_k) :=
  rfl

private theorem zProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hz : zVertex ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraBOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (zProjection data u) (zProjection data v) := by
  have hfinal := old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_z_only data hKS hK hnoY hnoX hz hu with
      ⟨d, rfl⟩ | ⟨p, rfl⟩ | rfl <;>
    rcases member_cases_z_only data hKS hK hnoY hnoX hz hv with
      ⟨e, rfl⟩ | ⟨q, rfl⟩ | rfl
  all_goals
    simp only [zProjection_core, zProjection_a, zProjection_z]
  · rw [specialLift_adj_core_core]
    exact (final_adj_core_core_iff data d e).1 hfinal
  · rw [specialLift_adj_core_a]
    exact (final_adj_core_a_iff data d q).1 hfinal
  · rw [specialLift_adj_core_b]
    exact (final_adj_z_core_iff data d).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_a]
    exact (final_adj_core_a_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [specialLift_adj_a_a]
    exact (final_adj_a_a_iff data p q).1 hfinal
  · rw [specialLift_adj_a_b]
    exact (final_adj_z_a_iff data p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_b]
    exact (final_adj_z_core_iff data e).1 hfinal
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_a_b]
    exact (final_adj_z_a_iff data q).1 hfinal
  · exact False.elim (huv.ne rfl)

private theorem card_lt_of_z_projection
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoX : xStar data ∉ K)
    (hz : zVertex ∈ K) :
    K.card < k := by
  let f := zProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraBOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      zProjection_maps_adj data hKS hK hnoY hnoX hz hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hfirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hfirst.1.cliqueFreeOn hK

private theorem c_adj_i2_of_large
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) (hp : 3 ≤ p.val) :
    G.Adj (data.cert.c p) (i2 data) := by
  have hp2 : p ≠ c2Index data := by
    intro h
    have hval := congrArg Fin.val h
    simp [c2Index, Certificates.c2Index] at hval
    omega
  have h := data.cert.caseB_adj_of_ne data.baseB hp2
  rw [Certificates.castIndex_c2'
    data.cert.five_le_k data.cert.five_le_s
    data.baseB.k_le_s] at h
  exact h

private theorem core_adj_i2_of_red_and_x
    (data : Certificates.PlusCaseBData G k s)
    {d : V}
    (hdred : redToWB data (Switching.Vertex.core d))
    (hdx : (extraBOldGraph data).Adj
      (Switching.Vertex.core d) (xStar data)) :
    G.Adj d (i2 data) := by
  rcases (redToWB_core data d).1 hdred with h | h
  · obtain ⟨p, rfl⟩ := h
    have hp2 : p ≠ c2Index data := by
      intro hp2
      subst p
      exact extraBOldGraph_not_adj_c2_xStar data hdx
    have hadj := data.cert.caseB_adj_of_ne data.baseB hp2
    rw [Certificates.castIndex_c2'
      data.cert.five_le_k data.cert.five_le_s
      data.baseB.k_le_s] at hadj
    exact hadj
  · exact h.symm

private theorem member_cases_x_no_a_no_z
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hnoZ : zVertex ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), 3 ≤ p.val ∧
      v = Switching.Vertex.b p) ∨
    v = xStar data := by
  rcases red_member_cases data (hKS hv) with
      h | h | h | h | h | h | h
  · obtain ⟨d, heq, _⟩ := h
    exact Or.inl ⟨d, heq⟩
  · obtain ⟨p, heq, _⟩ := h
    exact False.elim (hnoA p (by simpa [heq] using hv))
  · obtain ⟨p, heq, hp⟩ := h
    exact Or.inr (Or.inl ⟨p, hp, heq⟩)
  · exact Or.inr (Or.inr h)
  · exact False.elim (hnoY (some (i2Index data))
      (by simpa [h] using hv))
  · exact False.elim (hnoY none (by simpa [h] using hv))
  · exact False.elim (hnoZ (h ▸ hv))

private def xProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core d) => d
  | .inl (.a _) => .core (i2 data)
  | _ => .a (Certificates.c0Index data.cert.five_le_k)

@[simp]
private theorem xProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    xProjection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem xProjection_b
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    xProjection data (Switching.Vertex.b p) = .b p :=
  rfl

@[simp]
private theorem xProjection_xStar
    (data : Certificates.PlusCaseBData G k s) :
    xProjection data (xStar data) = .core (i2 data) := by
  simp [xProjection]

private theorem xProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (_hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hnoZ : zVertex ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraBOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (xProjection data u) (xProjection data v) := by
  have hfinal := old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_x_no_a_no_z data hKS hnoY hnoA hnoZ hu with
      ⟨d, rfl⟩ | ⟨p, hp, rfl⟩ | rfl <;>
    rcases member_cases_x_no_a_no_z data hKS hnoY hnoA hnoZ hv with
      ⟨e, rfl⟩ | ⟨q, hq, rfl⟩ | rfl
  all_goals
    simp only [xProjection_core, xProjection_b, xProjection_xStar]
  · rw [specialLift_adj_core_core]
    exact (final_adj_core_core_iff data d e).1 hfinal
  · rw [specialLift_adj_core_b]
    exact (final_adj_core_b_iff data d q).1 hfinal
  · rw [specialLift_adj_core_core]
    exact core_adj_i2_of_red_and_x data (hKS hu) huv
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_b]
    exact (final_adj_core_b_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · rw [specialLift_adj_b_b]
    exact (final_adj_b_b_iff_of_large data p q hp hq).1 hfinal
  · rw [(specialLift G data.cert.c).adj_comm,
      specialLift_adj_core_b]
    exact ⟨(data.cert.c_ne_i p (i2Index data)).symm,
      c_adj_i2_of_large data p hp⟩
  · rw [specialLift_adj_core_core]
    exact (core_adj_i2_of_red_and_x data
      (hKS hv) ((extraBOldGraph data).adj_symm huv)).symm
  · rw [specialLift_adj_core_b]
    exact ⟨(data.cert.c_ne_i q (i2Index data)).symm,
      c_adj_i2_of_large data q hq⟩
  · exact False.elim (huv.ne rfl)

private theorem card_lt_of_x_projection
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hnoZ : zVertex ∉ K) :
    K.card < k := by
  let f := xProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraBOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      xProjection_maps_adj data hKS hK hnoY hnoA hnoZ hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hfirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hfirst.1.cliqueFreeOn hK

private theorem member_cases_x_z_no_a
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hz : zVertex ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    v = xStar data ∨
    v = zVertex := by
  rcases red_member_cases data (hKS hv) with
      h | h | h | h | h | h | h
  · obtain ⟨d, heq, _⟩ := h
    exact Or.inl ⟨d, heq⟩
  · obtain ⟨p, heq, _⟩ := h
    exact False.elim (hnoA p (by simpa [heq] using hv))
  · obtain ⟨p, heq, hp⟩ := h
    have hb : Switching.Vertex.b p ∈ K := by
      simpa [heq] using hv
    exact False.elim (not_old_adj_z_b_of_large data hp
      (hK hz hb (by simp [zVertex])))
  · exact Or.inr (Or.inl h)
  · exact False.elim (hnoY (some (i2Index data))
      (by simpa [h] using hv))
  · exact False.elim (hnoY none (by simpa [h] using hv))
  · exact Or.inr (Or.inr h)

private def xzProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → V
  | .inl (.core (.core d)) => d
  | .inl (.a _) => i2 data
  | .inr _ => c0 data
  | _ => c0 data

@[simp]
private theorem xzProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    xzProjection data (Switching.Vertex.core d) = d :=
  rfl

@[simp]
private theorem xzProjection_xStar
    (data : Certificates.PlusCaseBData G k s) :
    xzProjection data (xStar data) = i2 data := by
  simp [xzProjection]

@[simp]
private theorem xzProjection_z
    (data : Certificates.PlusCaseBData G k s) :
    xzProjection data zVertex = c0 data :=
  rfl

private theorem xzProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hz : zVertex ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraBOldGraph data).Adj u v) :
    G.Adj (xzProjection data u) (xzProjection data v) := by
  have hfinal := old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_x_z_no_a data hKS hK hnoY hnoA hz hu with
      ⟨d, rfl⟩ | rfl | rfl <;>
    rcases member_cases_x_z_no_a data hKS hK hnoY hnoA hz hv with
      ⟨e, rfl⟩ | rfl | rfl
  all_goals
    simp only [xzProjection_core, xzProjection_xStar, xzProjection_z]
  · exact (final_adj_core_core_iff data d e).1 hfinal
  · exact core_adj_i2_of_red_and_x data (hKS hu) huv
  · exact ((final_adj_z_core_iff data d).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)).2.symm
  · exact (core_adj_i2_of_red_and_x data
      (hKS hv) ((extraBOldGraph data).adj_symm huv)).symm
  · exact False.elim (huv.ne rfl)
  · exact (c0_adj_i2 data).symm
  · exact ((final_adj_z_core_iff data e).1 hfinal).2
  · exact c0_adj_i2 data
  · exact False.elim (huv.ne rfl)

private theorem card_lt_of_xz_projection
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K)
    (hnoA : ∀ p : Fin (k - 1),
      Switching.Vertex.a p ∉ K)
    (hz : zVertex ∈ K) :
    K.card < k := by
  let f := xzProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraBOldGraph data).Adj u v → G.Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      xzProjection_maps_adj data hKS hK hnoY hnoA hz hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hG.1.cliqueFreeOn hK

private theorem card_coreIn_le_one_of_a
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    {p : Fin (k - 1)}
    (hp : Switching.Vertex.a p ∈ K) :
    Fintype.card (CoreIn K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro d e
  apply Subtype.ext
  have hdFinal := old_adj_implies_final data (hKS d.2) (hKS hp)
    (hK d.2 hp (by simp))
  have heFinal := old_adj_implies_final data (hKS e.2) (hKS hp)
    (hK e.2 hp (by simp))
  have hd := (final_adj_core_a_iff data d.1 p).1 hdFinal
  have he := (final_adj_core_a_iff data e.1 p).1 heFinal
  exact hd.symm.trans he

private theorem card_coreIn_eq_zero_of_two_a
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hAtwo : 2 ≤ Fintype.card (AIn K)) :
    Fintype.card (CoreIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro d
  have hAle : Fintype.card (AIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    have hpFinal := old_adj_implies_final data (hKS d.2) (hKS p.2)
      (hK d.2 p.2 (by simp))
    have hqFinal := old_adj_implies_final data (hKS d.2) (hKS q.2)
      (hK d.2 q.2 (by simp))
    have hp := (final_adj_core_a_iff data d.1 p.1).1 hpFinal
    have hq := (final_adj_core_a_iff data d.1 q.1).1 hqFinal
    exact data.cert.c.injective (hp.trans hq.symm)
  omega

private theorem card_bIn_eq_zero_of_z
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hz : zVertex ∈ K) :
    Fintype.card (BIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro p
  have hpLarge := (redToWB_b data p.1).1 (hKS p.2)
  exact not_old_adj_z_b_of_large data hpLarge
    (hK hz p.2 (by simp [zVertex]))

private theorem card_lt_of_no_y
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWB data v})
    (hK : (extraBOldGraph data).IsClique K)
    (hnoY : ∀ r : Option (Fin (s - 1)),
      Switching.Vertex.y data.cert r ∉ K) :
    K.card < k := by
  classical
  have hBlarge : ∀ p : BIn K, 3 ≤ p.1.val := by
    intro p
    exact (redToWB_b data p.1).1 (hKS p.2)
  have hBLe := card_largeB_le data hBlarge
  have hXLe : Fintype.card (XIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    calc
      r.1 = none :=
        x_index_eq_none_of_mem_red_neighborhood data hKS r.2
      _ = t.1 :=
        (x_index_eq_none_of_mem_red_neighborhood
          data hKS t.2).symm
  have hYZero : Fintype.card (YIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro r
    exact hnoY r.1 r.2
  have hZLe := card_zIn_le_one K
  have hparts := card_eq_six_blocks data.cert K
  have hk := data.cert.five_le_k
  by_cases hx : xStar data ∈ K
  · have ha0 := a0_not_mem_of_xStar data hKS hK hx
    have hAB :=
      card_aIn_add_card_bIn_le_sub_three data hKS hK ha0
    by_cases hz : zVertex ∈ K
    · have hBZero := card_bIn_eq_zero_of_z data hKS hK hz
      by_cases hAZero : Fintype.card (AIn K) = 0
      · have hnoA : ∀ p : Fin (k - 1),
            Switching.Vertex.a p ∉ K := by
          intro p hp
          have : Nonempty (AIn K) := ⟨⟨p, hp⟩⟩
          have hpos := Fintype.card_pos_iff.mpr this
          omega
        exact card_lt_of_xz_projection
          data hG hKS hK hnoY hnoA hz
      · by_cases hAOne : Fintype.card (AIn K) = 1
        · have hANonempty : Nonempty (AIn K) :=
            Fintype.card_pos_iff.mp (by omega)
          let p : AIn K := Classical.choice hANonempty
          have hCoreLe :=
            card_coreIn_le_one_of_a data hKS hK p.2
          omega
        · have hAtwo : 2 ≤ Fintype.card (AIn K) := by omega
          have hCoreZero :=
            card_coreIn_eq_zero_of_two_a data hKS hK hAtwo
          omega
    · have hZZero : Fintype.card (ZIn K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro z
        exact hz (by simpa using z.2)
      by_cases hAZero : Fintype.card (AIn K) = 0
      · have hnoA : ∀ p : Fin (k - 1),
            Switching.Vertex.a p ∉ K := by
          intro p hp
          have : Nonempty (AIn K) := ⟨⟨p, hp⟩⟩
          have hpos := Fintype.card_pos_iff.mpr this
          omega
        exact card_lt_of_x_projection
          data hG hKS hK hnoY hnoA hz
      · by_cases hAOne : Fintype.card (AIn K) = 1
        · have hANonempty : Nonempty (AIn K) :=
            Fintype.card_pos_iff.mp (by omega)
          let p : AIn K := Classical.choice hANonempty
          have hCoreLe :=
            card_coreIn_le_one_of_a data hKS hK p.2
          omega
        · have hAtwo : 2 ≤ Fintype.card (AIn K) := by omega
          have hCoreZero :=
            card_coreIn_eq_zero_of_two_a data hKS hK hAtwo
          omega
  · have hXZero : Fintype.card (XIn data.cert K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro r
      have hr :=
        x_index_eq_none_of_mem_red_neighborhood data hKS r.2
      exact hx (by simpa [xStar, hr] using r.2)
    by_cases hz : zVertex ∈ K
    · exact card_lt_of_z_projection data hG hKS hK hnoY hx hz
    · exact card_lt_of_lower_projection data hG hKS hK hnoY hx hz

/-- Type B has no red `K_k` inside the red neighborhood of the second
connector. -/
theorem redNeighborhoodB_cliqueFree
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    (extraBOldGraph data).CliqueFreeOn
      {v | redToWB data v} k := by
  classical
  intro K hKS hK
  have hlt : K.card < k := by
    by_cases hy2 : y2 data ∈ K
    · exact red_clique_card_lt_of_y2
        data hG hKS hK.isClique hy2
    · by_cases hyStar : yStar data ∈ K
      · exact red_clique_card_lt_of_yStar
          data hG hKS hK.isClique hyStar
      · have hnoY :
            ∀ r : Option (Fin (s - 1)),
              Switching.Vertex.y data.cert r ∉ K := by
          intro r hr
          have hrred : redToWB data
              (Switching.Vertex.y data.cert r) := hKS hr
          rcases (redToWB_y data r).1 hrred with h | h
          · subst r
            exact hyStar hr
          · subst r
            exact hy2 hr
        exact card_lt_of_no_y
          data hG hKS hK.isClique hnoY
  rw [hK.card_eq] at hlt
  exact (Nat.lt_irrefl k) hlt

end TypeB
end SecondConnector
end RamseyIncrement
