/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Projection
import RamseyIncrement.SecondConnector.TypeA.ChangedEdges

/-!
# Type A blue cliques through the second connector

This file formalizes the Type A blue-neighborhood analysis from the
strengthened second-connector argument.  The proof follows the three cases
in (22A), according as a blue clique in the blue neighborhood of `w`
contains at least two ordinary `X` vertices, exactly one, or none.
The no-`X` case uses the stated local projections into the original graph
or the first special lift.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeA

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private noncomputable abbrev BlueGraph
    (data : Certificates.PlusCaseAData G k s) :=
  (extraAOldGraph data)ᶜ

private abbrev i0
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.i (i0Index data)

private abbrev a2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c2Index data)

private abbrev b0
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.b (c0Index data)

private abbrev b1
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.b (c1Index data)

private abbrev i1Index
    (data : Certificates.PlusCaseAData G k s) :
    Fin (s - 1) :=
  Switching.Vertex.i1 data.cert

private theorem i0_ne_i1
    (data : Certificates.PlusCaseAData G k s) :
    i0Index data ≠ i1Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [i0Index, i1Index, Switching.Vertex.i1,
    Certificates.i0Index', Certificates.i1Index'] at hval

private theorem i0_ne_i2
    (data : Certificates.PlusCaseAData G k s) :
    i0Index data ≠ i2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [i0Index, i2Index, Certificates.i0Index',
    Certificates.i2Index'] at hval

private theorem i1_ne_i2
    (data : Certificates.PlusCaseAData G k s) :
    i1Index data ≠ i2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [i1Index, i2Index, Switching.Vertex.i1,
    Certificates.i1Index', Certificates.i2Index'] at hval

private theorem c0_ne_c1
    (data : Certificates.PlusCaseAData G k s) :
    c0Index data ≠ c1Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c0Index, c1Index, Certificates.c0Index,
    Certificates.c1Index] at hval

private theorem c0_ne_c2
    (data : Certificates.PlusCaseAData G k s) :
    c0Index data ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c0Index, c2Index, Certificates.c0Index,
    Certificates.c2Index] at hval

private theorem c1_ne_c2
    (data : Certificates.PlusCaseAData G k s) :
    c1Index data ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c1Index, c2Index, Certificates.c1Index,
    Certificates.c2Index] at hval

/-! ## The blue neighborhood and the reduction to the first connector -/

/-- Flat form of the blue neighborhood displayed in (22A). -/
private theorem blue_member_cases
    (data : Certificates.PlusCaseAData G k s)
    {v : Switching.Vertex V k s}
    (hv : ¬redToWA data v) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      (∀ p, d ≠ data.cert.c p) ∧ ¬G.Adj (i0 data) d) ∨
    v = a2 data ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.b p ∧ p ∉ Q data) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.x data.cert (some q)) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q) ∧
        q ≠ i0Index data ∧ q ≠ i2Index data) := by
  rcases vertex_six_block_cases data.cert v with
      h | h | h | h | h | h
  · obtain ⟨d, rfl⟩ := h
    rw [redToWA_core] at hv
    push Not at hv
    exact Or.inl ⟨d, rfl, hv.1, hv.2⟩
  · obtain ⟨p, rfl⟩ := h
    rw [redToWA_a] at hv
    push Not at hv
    subst p
    exact Or.inr (Or.inl rfl)
  · obtain ⟨p, rfl⟩ := h
    rw [redToWA_b] at hv
    exact Or.inr (Or.inr (Or.inl ⟨p, rfl, hv⟩))
  · obtain ⟨r, rfl⟩ := h
    rw [redToWA_x] at hv
    cases r with
    | none => exact False.elim (hv rfl)
    | some q =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
  · obtain ⟨r, rfl⟩ := h
    rw [redToWA_y] at hv
    push Not at hv
    cases r with
    | none => exact False.elim (hv.1 rfl)
    | some q =>
        refine Or.inr (Or.inr (Or.inr (Or.inr
          ⟨q, rfl, ?_, ?_⟩)))
        · intro hq
          exact hv.2.1 (congrArg some hq)
        · intro hq
          exact hv.2.2 (congrArg some hq)
  · subst v
    exact False.elim (hv (redToWA_z data))

/-- A blue `B`-index in (22A) is either one of the two small rows or
belongs to `P`. -/
private theorem b_index_cases
    (data : Certificates.PlusCaseAData G k s)
    {p : Fin (k - 1)}
    (hp : p ∉ Q data) :
    p = c0Index data ∨ p = c1Index data ∨ p ∈ P data := by
  by_cases hp2 : 2 ≤ p.val
  · by_cases hpP : p ∈ P data
    · exact Or.inr (Or.inr hpP)
    · exact False.elim
        (hp ((mem_Q data p).2 ⟨hp2, hpP⟩))
  · have hpSmall : p.val = 0 ∨ p.val = 1 := by omega
    rcases hpSmall with hp0 | hp1
    · left
      apply Fin.ext
      simpa [c0Index, Certificates.c0Index] using hp0
    · right
      left
      apply Fin.ext
      simpa [c1Index, Certificates.c1Index] using hp1

/-- Every edge made blue by (14A) has an endpoint which is red to `w`.
Hence a blue edge with both endpoints in (22A) was already blue in the
first-connector graph. -/
private theorem blue_adj_implies_final_blue
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (hu : ¬redToWA data u) (hv : ¬redToWA data v)
    (huv : (BlueGraph data).Adj u v) :
    (Switching.finalGraph data.cert)ᶜ.Adj u v := by
  by_contra hold
  have hchanged := classify_extraA_new_blue_edge data huv hold
  rcases hchanged with h | h | h
  · obtain ⟨p, hp, hpair⟩ := h
    rcases hpair with hpair | hpair
    · rcases hpair with ⟨rfl, rfl⟩
      exact hu ((redToWA_core data (data.cert.c p)).2
        (Or.inl ⟨p, rfl⟩))
    · rcases hpair with ⟨rfl, rfl⟩
      exact hv ((redToWA_core data (data.cert.c p)).2
        (Or.inl ⟨p, rfl⟩))
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hu ((redToWA_y data (some (i0Index data))).2
        (Or.inr (Or.inl rfl)))
    · rcases h with ⟨rfl, rfl⟩
      exact hv ((redToWA_y data (some (i0Index data))).2
        (Or.inr (Or.inl rfl)))
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hu ((redToWA_y data (some (i0Index data))).2
        (Or.inr (Or.inl rfl)))
    · rcases h with ⟨rfl, rfl⟩
      exact hv ((redToWA_y data (some (i0Index data))).2
        (Or.inr (Or.inl rfl)))

/-! ## First-connector blue adjacency equations -/

@[simp]
private theorem secondCertificate_some
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    Canonical.secondCertificate data.cert.toCertificates
        data.cert.five_le_k
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s)
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            data.cert.five_le_s)).symm (some q)) =
      .core (data.cert.i q) := by
  rw [Canonical.secondCertificate_apply]
  simp [Canonical.secondCertificateAt]

private theorem pre_blue_adj_x_lower_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (v : SpecialLiftVertex V k) :
    (Switching.preGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (.inl (.core v)) ↔
      Canonical.secondCertificateAt data.cert.toCertificates
        data.cert.five_le_k (some q) = v := by
  simp [Switching.preGraph, Switching.canonicalGraph, Canonical.graph,
    Switching.Vertex.x, Switching.redJoinedClone]
  change
    Canonical.secondCertificateAt data.cert.toCertificates
        data.cert.five_le_k
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            data.cert.five_le_s))
          ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              data.cert.five_le_s)).symm (some q))) = v ↔
      Canonical.secondCertificateAt data.cert.toCertificates
        data.cert.five_le_k (some q) = v
  simp

private theorem final_blue_adj_x_core_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (d : V) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.core d) ↔ d = data.cert.i q := by
  have hpre := pre_blue_adj_x_lower_iff data q
    (SpecialLiftVertex.core d)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [Switching.finalGraph, Switching.removedRedGraph,
    Switching.removedRedRel, Switching.addedRedGraph,
    Switching.addedRedRel, hpre, Switching.Vertex.x,
    Switching.Vertex.core, eq_comm]

private theorem final_blue_adj_x_a_iff
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    ¬(Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.a p) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  have hpre := pre_blue_adj_x_lower_iff data q
    (SpecialLiftVertex.a p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [Switching.finalGraph, Switching.removedRedGraph,
    Switching.removedRedRel, Switching.addedRedGraph,
    Switching.addedRedRel, hpre, Switching.Vertex.x,
    Switching.Vertex.a, hE]

private theorem final_blue_adj_x_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.b p) ↔
      q = i1Index data ∧ p = c0Index data := by
  have hpre := pre_blue_adj_x_lower_iff data q
    (SpecialLiftVertex.b p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [Switching.finalGraph, Switching.removedRedGraph,
    Switching.removedRedRel, Switching.addedRedGraph,
    Switching.addedRedRel, hpre, Switching.Vertex.x,
    Switching.Vertex.b, i1Index, c0Index,
    Switching.Vertex.i1, Switching.Vertex.c0]
  tauto

private theorem final_blue_adj_x_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (q r : Fin (s - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.y data.cert (some r)) ↔ q ≠ r := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.x, Switching.Vertex.y]

/-! ## At least two ordinary `X` vertices -/

private def xyIndex
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → Fin (s - 1)
  | .inl (.a q) =>
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s)) q |>.getD
        (i0Index data)
  | .inl (.b q) =>
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s)) q |>.getD
        (i0Index data)
  | _ => i0Index data

@[simp]
private theorem xyIndex_x
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    xyIndex data (Switching.Vertex.x data.cert (some q)) = q := by
  simp [xyIndex]

@[simp]
private theorem xyIndex_y
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    xyIndex data (Switching.Vertex.y data.cert (some q)) = q := by
  simp [xyIndex]

private theorem blue_clique_card_lt_of_two_x
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    {q r : Fin (s - 1)}
    (hqx : Switching.Vertex.x data.cert (some q) ∈ K)
    (hrx : Switching.Vertex.x data.cert (some r) ∈ K)
    (hqr : q ≠ r) :
    K.card < s := by
  classical
  have hqblue : ¬redToWA data
      (Switching.Vertex.x data.cert (some q)) := hKS hqx
  have hrblue : ¬redToWA data
      (Switching.Vertex.x data.cert (some r)) := hKS hrx
  have hcases : ∀ {v}, v ∈ K →
      (∃ t : Fin (s - 1),
        v = Switching.Vertex.x data.cert (some t)) ∨
      (∃ t : Fin (s - 1),
        v = Switching.Vertex.y data.cert (some t)) := by
    intro v hv
    have hvblue := hKS hv
    rcases blue_member_cases data hvblue with
        hcore | ha | hb | hx | hy
    · obtain ⟨d, rfl, _, _⟩ := hcore
      have hqd := (final_blue_adj_x_core_iff data q d).1
        (blue_adj_implies_final_blue data hqblue hvblue
          (hK hqx hv (by simp)))
      have hrd := (final_blue_adj_x_core_iff data r d).1
        (blue_adj_implies_final_blue data hrblue hvblue
          (hK hrx hv (by simp)))
      exact False.elim
        (hqr (data.cert.i.injective (hqd.symm.trans hrd)))
    · subst v
      exact False.elim
        (final_blue_adj_x_a_iff data hG q (c2Index data)
          (blue_adj_implies_final_blue data hqblue hvblue
            (hK hqx hv (by simp))))
    · obtain ⟨p, rfl, hpQ⟩ := hb
      have hqb := (final_blue_adj_x_b_iff data q p).1
        (blue_adj_implies_final_blue data hqblue hvblue
          (hK hqx hv (by simp)))
      have hrb := (final_blue_adj_x_b_iff data r p).1
        (blue_adj_implies_final_blue data hrblue hvblue
          (hK hrx hv (by simp)))
      exact False.elim (hqr (hqb.1.trans hrb.1.symm))
    · exact Or.inl hx
    · exact Or.inr ⟨hy.choose, hy.choose_spec.1⟩
  have hinj : Function.Injective
      (fun v : {v // v ∈ K} ↦ xyIndex data v.1) := by
    intro u v huv
    rcases hcases u.2 with ⟨p, hp⟩ | ⟨p, hp⟩ <;>
      rcases hcases v.2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hpt : p = t := by simpa [hp, ht] using huv
      subst t
      apply Subtype.ext
      exact hp.trans ht.symm
    · have hpt : p = t := by simpa [hp, ht] using huv
      subst t
      have hne : (u : Switching.Vertex V k s) ≠ v := by
        rw [hp, ht]
        simp [Switching.Vertex.x, Switching.Vertex.y]
      have hfinal := blue_adj_implies_final_blue data
        (hKS u.2) (hKS v.2) (hK u.2 v.2 hne)
      rw [hp, ht] at hfinal
      exact False.elim
        ((final_blue_adj_x_y_iff data p p).1 hfinal rfl)
    · have hpt : p = t := by simpa [hp, ht] using huv
      subst t
      have hne : (u : Switching.Vertex V k s) ≠ v := by
        rw [hp, ht]
        simp [Switching.Vertex.x, Switching.Vertex.y]
      have hfinal := blue_adj_implies_final_blue data
        (hKS u.2) (hKS v.2) (hK u.2 v.2 hne)
      rw [hp, ht] at hfinal
      exact False.elim
        ((final_blue_adj_x_y_iff data p p).1
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal) rfl)
    · have hpt : p = t := by simpa [hp, ht] using huv
      subst t
      apply Subtype.ext
      exact hp.trans ht.symm
  have hcard : K.card ≤ s - 1 := by
    rw [← Fintype.card_coe]
    simpa using Fintype.card_le_of_injective
      (fun v : {v // v ∈ K} ↦ xyIndex data v.1) hinj
  have hs := data.cert.five_le_s
  omega

/-! ## Exactly one ordinary `X` vertex -/

private def ySet
    (data : Certificates.PlusCaseAData G k s)
    (Q : Finset (Fin (s - 1))) :
    Finset (Switching.Vertex V k s) :=
  Q.map
    ⟨fun q ↦ Switching.Vertex.y data.cert (some q),
      fun _ _ h ↦ Option.some.inj (vertex_y_injective data.cert h)⟩

@[simp]
private theorem mem_ySet
    (data : Certificates.PlusCaseAData G k s)
    (Q : Finset (Fin (s - 1))) (q : Fin (s - 1)) :
    Switching.Vertex.y data.cert (some q) ∈ ySet data Q ↔ q ∈ Q := by
  simp [ySet]

@[simp]
private theorem card_ySet
    (data : Certificates.PlusCaseAData G k s)
    (Q : Finset (Fin (s - 1))) :
    (ySet data Q).card = Q.card := by
  simp [ySet]

private noncomputable def yIndices
    (data : Certificates.PlusCaseAData G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Finset (Fin (s - 1)) := by
  classical
  exact Finset.univ.filter fun q ↦
    Switching.Vertex.y data.cert (some q) ∈ K

@[simp]
private theorem mem_yIndices
    (data : Certificates.PlusCaseAData G k s)
    (K : Finset (Switching.Vertex V k s)) (q : Fin (s - 1)) :
    q ∈ yIndices data K ↔
      Switching.Vertex.y data.cert (some q) ∈ K := by
  simp [yIndices]

private theorem yIndices_card_le_away_zero_two
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v}) :
    (yIndices data K).card ≤ s - 3 := by
  classical
  let U : Finset (Fin (s - 1)) :=
    (Finset.univ.erase (i0Index data)).erase (i2Index data)
  have hsub : yIndices data K ⊆ U := by
    intro q hq
    have hy := (mem_yIndices data K q).1 hq
    have hblue := hKS hy
    change ¬redToWA data
      (Switching.Vertex.y data.cert (some q)) at hblue
    rw [redToWA_y] at hblue
    push Not at hblue
    simp only [U, Finset.mem_erase, Finset.mem_univ, and_true]
    exact
      ⟨fun h ↦ hblue.2.2 (congrArg some h),
        fun h ↦ hblue.2.1 (congrArg some h)⟩
  have hc := Finset.card_le_card hsub
  have hi0 :
      i0Index data ∈ (Finset.univ : Finset (Fin (s - 1))) := by simp
  have hi2 :
      i2Index data ∈
        (Finset.univ : Finset (Fin (s - 1))).erase (i0Index data) := by
    exact Finset.mem_erase.mpr
      ⟨(i0_ne_i2 data).symm, Finset.mem_univ _⟩
  have hUcard : U.card = s - 3 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hi2,
      Finset.card_erase_of_mem hi0]
    simp
    have hs := data.cert.five_le_s
    omega
  simpa [hUcard] using hc

private theorem yIndices_card_le_away_zero_one_two
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hx1 : Switching.Vertex.x data.cert (some (i1Index data)) ∈ K) :
    (yIndices data K).card ≤ s - 4 := by
  classical
  let U : Finset (Fin (s - 1)) :=
    ((Finset.univ.erase (i0Index data)).erase
      (i2Index data)).erase (i1Index data)
  have hsub : yIndices data K ⊆ U := by
    intro q hq
    have hy := (mem_yIndices data K q).1 hq
    have hblue := hKS hy
    change ¬redToWA data
      (Switching.Vertex.y data.cert (some q)) at hblue
    rw [redToWA_y] at hblue
    push Not at hblue
    have hq1 : q ≠ i1Index data := by
      intro h
      subst q
      have hedge := hK hx1 hy (by
        simp [Switching.Vertex.x, Switching.Vertex.y])
      have hfinal := blue_adj_implies_final_blue data (hKS hx1) (hKS hy)
        hedge
      exact (final_blue_adj_x_y_iff data
        (i1Index data) (i1Index data)).1 hfinal rfl
    simp only [U, Finset.mem_erase, Finset.mem_univ, and_true]
    exact
      ⟨hq1,
        fun h ↦ hblue.2.2 (congrArg some h),
        fun h ↦ hblue.2.1 (congrArg some h)⟩
  have hc := Finset.card_le_card hsub
  have hi0 :
      i0Index data ∈ (Finset.univ : Finset (Fin (s - 1))) := by simp
  have hi2 :
      i2Index data ∈
        (Finset.univ : Finset (Fin (s - 1))).erase (i0Index data) := by
    exact Finset.mem_erase.mpr
      ⟨(i0_ne_i2 data).symm, Finset.mem_univ _⟩
  have hi1 :
      i1Index data ∈
        ((Finset.univ : Finset (Fin (s - 1))).erase
          (i0Index data)).erase (i2Index data) := by
    exact Finset.mem_erase.mpr
      ⟨i1_ne_i2 data,
        Finset.mem_erase.mpr
          ⟨(i0_ne_i1 data).symm, Finset.mem_univ _⟩⟩
  have hUcard : U.card = s - 4 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem hi1,
      Finset.card_erase_of_mem hi2,
      Finset.card_erase_of_mem hi0]
    simp
    have hs := data.cert.five_le_s
    omega
  simpa [hUcard] using hc

private theorem blue_clique_card_lt_of_one_x
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (r : Fin (s - 1))
    (hxr : Switching.Vertex.x data.cert (some r) ∈ K)
    (honly : ∀ t : Fin (s - 1),
      Switching.Vertex.x data.cert (some t) ∈ K → t = r) :
    K.card < s := by
  classical
  let Q := yIndices data K
  have hxblue : ¬redToWA data
      (Switching.Vertex.x data.cert (some r)) := hKS hxr
  by_cases hr1 : r = i1Index data
  · subst r
    have hQcard : Q.card ≤ s - 4 :=
      yIndices_card_le_away_zero_one_two data hKS hK hxr
    have hsub :
        K ⊆ insert
          (Switching.Vertex.x data.cert (some (i1Index data)))
          (insert (Switching.Vertex.core (data.cert.i (i1Index data)))
            (insert (b0 data) (ySet data Q))) := by
      intro v hv
      have hvblue := hKS hv
      rcases blue_member_cases data hvblue with
          hcore | ha | hb | hx | hy
      · obtain ⟨d, rfl, _, _⟩ := hcore
        have hxd := (final_blue_adj_x_core_iff data (i1Index data) d).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        subst d
        simp
      · subst v
        exact False.elim
          (final_blue_adj_x_a_iff data hG (i1Index data) (c2Index data)
            (blue_adj_implies_final_blue data hxblue hvblue
              (hK hxr hv (by simp))))
      · obtain ⟨p, rfl, hpQ⟩ := hb
        have hxb := (final_blue_adj_x_b_iff data (i1Index data) p).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        rw [hxb.2]
        simp [b0]
      · obtain ⟨t, rfl⟩ := hx
        have ht := honly t hv
        subst t
        simp
      · obtain ⟨q, rfl, _, _⟩ := hy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              ((mem_ySet data Q q).2 ((mem_yIndices data K q).2 hv))))
    have hc := Finset.card_le_card hsub
    have hA := Finset.card_insert_le
      (Switching.Vertex.x data.cert (some (i1Index data)))
      (insert (Switching.Vertex.core (data.cert.i (i1Index data)))
        (insert (b0 data) (ySet data Q)))
    have hB := Finset.card_insert_le
      (Switching.Vertex.core (data.cert.i (i1Index data)))
      (insert (b0 data) (ySet data Q))
    have hC := Finset.card_insert_le (b0 data) (ySet data Q)
    rw [card_ySet] at hC
    have hs := data.cert.five_le_s
    omega
  · have hQcard : Q.card ≤ s - 3 :=
      yIndices_card_le_away_zero_two data hKS
    have hsub :
        K ⊆ insert (Switching.Vertex.x data.cert (some r))
          (insert (Switching.Vertex.core (data.cert.i r))
            (ySet data Q)) := by
      intro v hv
      have hvblue := hKS hv
      rcases blue_member_cases data hvblue with
          hcore | ha | hb | hx | hy
      · obtain ⟨d, rfl, _, _⟩ := hcore
        have hxd := (final_blue_adj_x_core_iff data r d).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        subst d
        simp
      · subst v
        exact False.elim
          (final_blue_adj_x_a_iff data hG r (c2Index data)
            (blue_adj_implies_final_blue data hxblue hvblue
              (hK hxr hv (by simp))))
      · obtain ⟨p, rfl, hpQ⟩ := hb
        have hxb := (final_blue_adj_x_b_iff data r p).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        exact False.elim (hr1 hxb.1)
      · obtain ⟨t, rfl⟩ := hx
        have ht := honly t hv
        subst t
        simp
      · obtain ⟨q, rfl, _, _⟩ := hy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            ((mem_ySet data Q q).2 ((mem_yIndices data K q).2 hv))
          )
    have hc := Finset.card_le_card hsub
    have hA := Finset.card_insert_le
      (Switching.Vertex.x data.cert (some r))
      (insert (Switching.Vertex.core (data.cert.i r)) (ySet data Q))
    have hB := Finset.card_insert_le
      (Switching.Vertex.core (data.cert.i r)) (ySet data Q)
    rw [card_ySet] at hB
    have hs := data.cert.five_le_s
    omega

/-! ## No ordinary `X` vertices: common projection infrastructure -/

/-- Project an ordinary `y_q` to `i_q` and otherwise forget the outer
lift and clone tags. -/
private def oldProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core v) => v
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some r => .core (data.cert.i r)
      | none => .core (i0 data)
  | _ => .core (i0 data)

@[simp]
private theorem oldProjection_core
    (data : Certificates.PlusCaseAData G k s) (d : V) :
    oldProjection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem oldProjection_a
    (data : Certificates.PlusCaseAData G k s) (p : Fin (k - 1)) :
    oldProjection data (Switching.Vertex.a p) = .a p :=
  rfl

@[simp]
private theorem oldProjection_b
    (data : Certificates.PlusCaseAData G k s) (p : Fin (k - 1)) :
    oldProjection data (Switching.Vertex.b p) = .b p :=
  rfl

@[simp]
private theorem oldProjection_y
    (data : Certificates.PlusCaseAData G k s) (q : Fin (s - 1)) :
    oldProjection data (Switching.Vertex.y data.cert (some q)) =
      .core (data.cert.i q) := by
  simp [oldProjection]

@[simp]
private theorem oldProjection_lower
    (data : Certificates.PlusCaseAData G k s)
    (d : SpecialLiftVertex V k) :
    oldProjection data (Switching.Vertex.lower d) = d := by
  cases d <;> rfl

/-- A final-blue edge with two lower endpoints is a blue edge of the
first lift. -/
private theorem final_blue_lower_lower_to_first
    (data : Certificates.PlusCaseAData G k s)
    {d e : SpecialLiftVertex V k}
    (hblue : (Switching.finalGraph data.cert)ᶜ.Adj
      (Switching.Vertex.lower d) (Switching.Vertex.lower e)) :
    (specialLift G data.cert.c)ᶜ.Adj d e := by
  have hsource :
      (Switching.preGraph data.cert)ᶜ.Adj
        (Switching.Vertex.lower d) (Switching.Vertex.lower e) := by
    by_contra h
    have hrem := Switching.classify_new_blue_edge data.cert hblue h
    simp [Switching.removedRedGraph_adj_iff,
      Switching.SymmPair] at hrem
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, ?_⟩
  · intro hde
    subst e
    exact (Switching.finalGraph data.cert)ᶜ.loopless.irrefl _ hblue
  · intro hred
    exact ((SimpleGraph.compl_adj _ _ _).1 hsource).2
      ((Switching.preGraph_adj_lower_lower_iff data.cert d e).2 hred)

/-- Except for `b₀`, a final-blue lower/ordinary-`Y` edge projects to a
blue edge of the first lift. -/
private theorem final_blue_lower_y_to_first
    (data : Certificates.PlusCaseAData G k s)
    {d : SpecialLiftVertex V k} {q : Fin (s - 1)}
    (hd0 : (Switching.Vertex.lower d :
        Switching.Vertex V k s) ≠ b0 data)
    (hblue : (Switching.finalGraph data.cert)ᶜ.Adj
      (Switching.Vertex.lower d)
      (Switching.Vertex.y data.cert (some q))) :
    (specialLift G data.cert.c)ᶜ.Adj d
      (.core (data.cert.i q)) := by
  have hsource :
      (Switching.preGraph data.cert)ᶜ.Adj
        (Switching.Vertex.lower d)
        (Switching.Vertex.y data.cert (some q)) := by
    by_contra h
    have hrem := Switching.classify_new_blue_edge data.cert hblue h
    simp [Switching.removedRedGraph_adj_iff,
      Switching.SymmPair] at hrem
    apply hd0
    simp [hrem.2]
  have hnot := ((SimpleGraph.compl_adj _ _ _).1 hsource).2
  rw [Switching.preGraph_adj_lower_y_iff] at hnot
  rw [SimpleGraph.compl_adj]
  constructor
  · intro heq
    exact hnot (Or.inl (by
      simpa [Canonical.secondCertificateAt] using heq))
  · intro hadj
    exact hnot (Or.inr (by
      simpa [Canonical.secondCertificateAt] using hadj.symm))

private theorem i_compl_adj
    (data : Certificates.PlusCaseAData G k s)
    {q r : Fin (s - 1)} (hqr : q ≠ r) :
    Gᶜ.Adj (data.cert.i q) (data.cert.i r) :=
  data.cert.i_compl_adj hqr

private theorem noX_member_lower_or_y
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : SpecialLiftVertex V k,
      v = Switching.Vertex.lower d) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q)) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · obtain ⟨d, rfl, _, _⟩ := hcore
    exact Or.inl ⟨.core d, rfl⟩
  · subst v
    exact Or.inl ⟨.a (c2Index data), rfl⟩
  · obtain ⟨p, rfl, _⟩ := hb
    exact Or.inl ⟨.b p, rfl⟩
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · obtain ⟨q, rfl, _, _⟩ := hy
    exact Or.inr ⟨q, rfl⟩

private theorem oldProjection_maps_adj_without_b0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (oldProjection data u) (oldProjection data v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases noX_member_lower_or_y data hKS hnoX hu with
      ⟨d, rfl⟩ | ⟨q, rfl⟩ <;>
    rcases noX_member_lower_or_y data hKS hnoX hv with
      ⟨e, rfl⟩ | ⟨r, rfl⟩
  · simpa only [oldProjection_lower] using
      final_blue_lower_lower_to_first data hfinal
  ·
    have hd0 :
        (Switching.Vertex.lower d :
          Switching.Vertex V k s) ≠ b0 data := by
      intro hd
      exact hb0K (by simpa [hd] using hu)
    simpa only [oldProjection_lower, oldProjection_y] using
      final_blue_lower_y_to_first data hd0 hfinal
  ·
    have he0 :
        (Switching.Vertex.lower e :
          Switching.Vertex V k s) ≠ b0 data := by
      intro he
      exact hb0K (by simpa [he] using hv)
    simpa only [oldProjection_lower, oldProjection_y] using
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
  ·
    have hqr : q ≠ r := by
      intro h
      subst r
      exact (Switching.finalGraph data.cert)ᶜ.loopless.irrefl _ hfinal
    simpa only [oldProjection_y,
      specialLift_compl_adj_core_core] using i_compl_adj data hqr

/-! ## Clique-local injectivity tools -/

private theorem card_lt_of_blue_projection
    {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (f : Switching.Vertex V k s → W)
    (hK : (BlueGraph data).IsClique K)
    (hadj : ∀ {u v}, u ∈ K → v ∈ K →
      (BlueGraph data).Adj u v → H.Adj (f u) (f v))
    (hfree : H.CliqueFree n) :
    K.card < n := by
  classical
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    have hedge := hadj hu hv (hK hu hv hne)
    rw [huv] at hedge
    exact H.loopless.irrefl _ hedge
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    (fun {_ _} hu hv huv ↦ hadj hu hv huv)
    hfree.cliqueFreeOn hK

private theorem card_succ_lt_of_blue_projection
    {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (f : Switching.Vertex V k s → W) (extra : W)
    (hK : (BlueGraph data).IsClique K)
    (hadj : ∀ {u v}, u ∈ K → v ∈ K →
      (BlueGraph data).Adj u v → H.Adj (f u) (f v))
    (hadjoin : ∀ {u}, u ∈ K → H.Adj (f u) extra)
    (hfree : H.CliqueFree n) :
    K.card + 1 < n := by
  classical
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    have hedge := hadj hu hv (hK hu hv hne)
    rw [huv] at hedge
    exact H.loopless.irrefl _ hedge
  have hneExtra {u : Switching.Vertex V k s} (hu : u ∈ K) :
      f u ≠ extra := by
    intro hue
    have hedge := hadjoin hu
    rw [hue] at hedge
    exact H.loopless.irrefl _ hedge
  let e : ({v // v ∈ K} ⊕ Unit) ↪ W :=
    { toFun := fun x =>
        match x with
        | Sum.inl v => f v.1
        | Sum.inr _ => extra
      inj' := by
        intro u v huv
        rcases u with u | u <;> rcases v with v | v
        · apply congrArg Sum.inl
          apply Subtype.ext
          exact hinj u.2 v.2 huv
        · exact False.elim (hneExtra u.2 huv)
        · exact False.elim (hneExtra v.2 huv.symm)
        · exact congrArg Sum.inr (Subsingleton.elim u v) }
  have hclique :
      ∀ u v : ({v // v ∈ K} ⊕ Unit), u ≠ v →
        H.Adj (e u) (e v) := by
    intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · apply hadj u.2 v.2
      apply hK u.2 v.2
      intro heq
      exact huv (congrArg Sum.inl (Subtype.ext heq))
    · exact hadjoin u.2
    · exact H.adj_symm (hadjoin v.2)
    · exact False.elim
        (huv (congrArg Sum.inr (Subsingleton.elim u v)))
  have hlt := card_lt_of_cliqueFree_of_embedding hfree e hclique
  simpa using hlt

/-! ## No `X`, no small `B` -/

/-- The added edge `i₀a₂` is red in the edited old graph. -/
private theorem not_blue_i0_a2
    (data : Certificates.PlusCaseAData G k s) :
    ¬(BlueGraph data).Adj
      (Switching.Vertex.core (i0 data)) (a2 data) := by
  intro hblue
  have hadd :
      (extraAAddedRedGraph data).Adj
        (Switching.Vertex.core (i0 data)) (a2 data) := by
    rw [extraAAddedRedGraph_adj_iff]
    exact Or.inl ⟨rfl, rfl⟩
  have hred := extraAOldGraph_adj_of_added data hadd
  exact ((SimpleGraph.compl_adj _ _ _).1 hblue).2 hred

private theorem noX_noSmall_noI0_card_lt
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi0K : Switching.Vertex.core (i0 data) ∉ K) :
    K.card < s := by
  classical
  have hadj :
      ∀ {u v}, u ∈ K → v ∈ K →
        (BlueGraph data).Adj u v →
        (specialLift G data.cert.c)ᶜ.Adj
          (oldProjection data u) (oldProjection data v) :=
    fun {_ _} hu hv huv ↦
      oldProjection_maps_adj_without_b0
        data hKS hnoX hb0K hu hv huv
  have hadjoin :
      ∀ {u}, u ∈ K →
        (specialLift G data.cert.c)ᶜ.Adj
          (oldProjection data u) (.core (i0 data)) := by
    intro u hu
    rcases blue_member_cases data (hKS hu) with
        hcore | ha | hb | hx | hy
    · obtain ⟨d, rfl, _, hdblue⟩ := hcore
      rw [oldProjection_core, specialLift_compl_adj_core_core,
        SimpleGraph.compl_adj]
      constructor
      · intro hdi
        subst d
        exact hi0K hu
      · simpa [G.adj_comm] using hdblue
    · subst u
      rw [oldProjection_a, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i (c2Index data) (i0Index data)
    · obtain ⟨p, rfl, hpQ⟩ := hb
      rcases b_index_cases data hpQ with hp0 | hp1 | hpP
      · subst p
        exact False.elim (hb0K hu)
      · subst p
        exact False.elim (hb1K hu)
      · rw [oldProjection_b, specialLift_compl_adj_b_core]
        right
        rw [SimpleGraph.compl_adj]
        exact ⟨data.cert.c_ne_i p (i0Index data),
          (mem_P data p).1 hpP⟩
    · obtain ⟨q, rfl⟩ := hx
      exact False.elim (hnoX q hu)
    · obtain ⟨q, rfl, hq0, _⟩ := hy
      rw [oldProjection_y, specialLift_compl_adj_core_core]
      exact i_compl_adj data hq0
  have hfirst :
      IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  have hlt :
      K.card + 1 < s + 1 :=
    card_succ_lt_of_blue_projection data
      (oldProjection data) (.core (i0 data))
      hK hadj hadjoin hfirst.2
  omega

/-- Projection used when `i₀` occurs: core vertices are retained,
ordinary `y_q` goes to `i_q`, and a possible large `b_p` goes to `c_p`. -/
private def baseProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → V
  | .inl (.core (.core d)) => d
  | .inl (.core (.b p)) => data.cert.c p
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some r => data.cert.i r
      | none => i0 data
  | _ => i0 data

@[simp]
private theorem baseProjection_core
    (data : Certificates.PlusCaseAData G k s) (d : V) :
    baseProjection data (Switching.Vertex.core d) = d :=
  rfl

@[simp]
private theorem baseProjection_b
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    baseProjection data (Switching.Vertex.b p) = data.cert.c p :=
  rfl

@[simp]
private theorem baseProjection_y
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    baseProjection data
        (Switching.Vertex.y data.cert (some q)) = data.cert.i q := by
  simp [baseProjection]

private theorem noX_noSmall_i0_member_cases
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi0K : Switching.Vertex.core (i0 data) ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ∀ p, d ≠ data.cert.c p) ∨
    (∃ p ∈ P data, v = Switching.Vertex.b p) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q)) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · obtain ⟨d, heq, hdC, _⟩ := hcore
    exact Or.inl ⟨d, heq, hdC⟩
  · subst v
    have hblue := hK hi0K hv (by simp [a2])
    exact False.elim (not_blue_i0_a2 data hblue)
  · obtain ⟨p, rfl, hpQ⟩ := hb
    rcases b_index_cases data hpQ with hp0 | hp1 | hpP
    · subst p
      exact False.elim (hb0K hv)
    · subst p
      exact False.elim (hb1K hv)
    · exact Or.inr (Or.inl ⟨p, hpP, rfl⟩)
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · obtain ⟨q, heq, _, _⟩ := hy
    exact Or.inr (Or.inr ⟨q, heq⟩)

private theorem baseProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi0K : Switching.Vertex.core (i0 data) ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    Gᶜ.Adj (baseProjection data u) (baseProjection data v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases noX_noSmall_i0_member_cases
      data hKS hK hnoX hb0K hb1K hi0K hu with
      ⟨d, rfl, hdC⟩ | ⟨p, hpP, rfl⟩ | ⟨q, rfl⟩ <;>
    rcases noX_noSmall_i0_member_cases
      data hKS hK hnoX hb0K hb1K hi0K hv with
      ⟨e, rfl, heC⟩ | ⟨r, hrP, rfl⟩ | ⟨t, rfl⟩
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    simpa only [baseProjection_core,
      specialLift_compl_adj_core_core] using hfirst
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_core_b] at hfirst
    rcases hfirst with hdc | hdc
    · exact False.elim (hdC r hdc)
    · simpa only [baseProjection_core, baseProjection_b] using
        Gᶜ.adj_symm hdc
  ·
    have hd0 :
        (Switching.Vertex.lower (.core d) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    have hfirst := final_blue_lower_y_to_first data hd0 hfinal
    simpa only [baseProjection_core, baseProjection_y,
      specialLift_compl_adj_core_core] using hfirst
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_b_core] at hfirst
    rcases hfirst with hec | hec
    · exact False.elim (heC p hec)
    · simpa only [baseProjection_b, baseProjection_core] using hec
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_b_b] at hfirst
    have hp2 := (mem_largeRows data p).1
      (P_subset_largeRows data hpP)
    have hr2 := (mem_largeRows data r).1
      (P_subset_largeRows data hrP)
    exact False.elim (hfirst.2 (by
      simp [SameBPart]
      omega))
  ·
    have hp0 : p ≠ c0Index data :=
      fun h ↦ c0_not_mem_P data (h ▸ hpP)
    have hlower0 :
        (Switching.Vertex.lower (.b p) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hp :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact hp0 hp
    have hfirst :=
      final_blue_lower_y_to_first data hlower0 hfinal
    rw [specialLift_compl_adj_b_core] at hfirst
    rcases hfirst with hic | hic
    · exact False.elim
        (data.cert.c_ne_i p t hic.symm)
    · simpa only [baseProjection_b, baseProjection_y] using hic
  ·
    have he0 :
        (Switching.Vertex.lower (.core e) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    have hfirst :=
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
    simpa only [baseProjection_y, baseProjection_core,
      specialLift_compl_adj_core_core] using hfirst
  ·
    have hr0 : r ≠ c0Index data :=
      fun h ↦ c0_not_mem_P data (h ▸ hrP)
    have hlower0 :
        (Switching.Vertex.lower (.b r) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hr :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact hr0 hr
    have hfirst :=
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data hlower0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
    rw [specialLift_compl_adj_core_b] at hfirst
    rcases hfirst with hic | hic
    · exact False.elim
        (data.cert.c_ne_i r q hic.symm)
    · simpa only [baseProjection_y, baseProjection_b] using
        Gᶜ.adj_symm hic
  ·
    have hqt : q ≠ t := by
      intro h
      subst t
      exact (Switching.finalGraph data.cert)ᶜ.loopless.irrefl _ hfinal
    simpa only [baseProjection_y] using i_compl_adj data hqt

private theorem noX_noSmall_i0_card_lt
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi0K : Switching.Vertex.core (i0 data) ∈ K) :
    K.card < s := by
  exact card_lt_of_blue_projection data (baseProjection data) hK
    (fun {_ _} hu hv huv ↦
      baseProjection_maps_adj
        data hKS hK hnoX hb0K hb1K hi0K hu hv huv)
    hG.2

/-! ## No `X`, with one small `B` -/

private theorem small_index_val_lt_two
    (data : Certificates.PlusCaseAData G k s)
    {r : Fin (k - 1)}
    (hr : r = c0Index data ∨ r = c1Index data) :
    r.val < 2 := by
  rcases hr with rfl | rfl <;>
    simp [c0Index, c1Index, Certificates.c0Index,
      Certificates.c1Index]

private theorem small_b_index_unique
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    {r q : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hqSmall : q = c0Index data ∨ q = c1Index data)
    (hr : Switching.Vertex.b r ∈ K)
    (hq : Switching.Vertex.b q ∈ K) :
    q = r := by
  by_contra hqr
  have hblue := hK hq hr (by simpa using hqr)
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hq) (hKS hr) hblue
  have hfirst := final_blue_lower_lower_to_first data hfinal
  rw [specialLift_compl_adj_b_b] at hfirst
  exact hfirst.2 (Or.inl
    ⟨small_index_val_lt_two data hqSmall,
      small_index_val_lt_two data hrSmall⟩)

private theorem large_b_index_unique
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    {p q : Fin (k - 1)}
    (hpP : p ∈ P data) (hqP : q ∈ P data)
    (hp : Switching.Vertex.b p ∈ K)
    (hq : Switching.Vertex.b q ∈ K) :
    q = p := by
  by_contra hqp
  have hblue := hK hq hp (by simpa using hqp)
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hq) (hKS hp) hblue
  have hfirst := final_blue_lower_lower_to_first data hfinal
  rw [specialLift_compl_adj_b_b] at hfirst
  have hp2 := (mem_largeRows data p).1
    (P_subset_largeRows data hpP)
  have hq2 := (mem_largeRows data q).1
    (P_subset_largeRows data hqP)
  exact hfirst.2 (Or.inr ⟨hq2, hp2⟩)

private theorem small_b_excludes_i0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    {r : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K) :
    Switching.Vertex.core (i0 data) ∉ K := by
  intro hi0
  have hblue := hK hr hi0 (by simp)
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hr) (hKS hi0) hblue
  have hfirst := final_blue_lower_lower_to_first data hfinal
  rw [specialLift_compl_adj_b_core] at hfirst
  rcases hfirst with heq | hcomp
  · exact (data.cert.c_ne_i r (i0Index data)) heq.symm
  ·
    have hred : G.Adj (data.cert.c r) (i0 data) := by
      rcases hrSmall with rfl | rfl
      · exact data.c0_i0_red
      · exact data.c1_i0_red
    exact ((SimpleGraph.compl_adj _ _ _).1 hcomp).2 hred

private theorem small_b_excludes_a2
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    {r : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K) :
    a2 data ∉ K := by
  intro ha2
  have hblue := hK hr ha2 (by simp [a2])
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hr) (hKS ha2) hblue
  have hfirst := final_blue_lower_lower_to_first data hfinal
  rw [specialLift_compl_adj_b_a] at hfirst
  rcases hrSmall with rfl | rfl
  · exact (c0_ne_c2 data) hfirst.symm
  · exact (c1_ne_c2 data) hfirst.symm

/-- Replace the occurring small `b_r` by `a_t`, retain all other lower
vertices, and project ordinary `y_q` to `i_q`.  In the no-large case
`t=r`; in the large case `t=p` for the unique occurring `p ∈ P`. -/
private def smallProjection
    (data : Certificates.PlusCaseAData G k s)
    (r t : Fin (k - 1)) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core d)) => .core d
  | .inl (.core (.a p)) => .a p
  | .inl (.core (.b p)) =>
      if p = r then .a t else .b p
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some p => .core (data.cert.i p)
      | none => .core (i0 data)
  | _ => .core (i0 data)

@[simp]
private theorem smallProjection_core
    (data : Certificates.PlusCaseAData G k s)
    (r t : Fin (k - 1)) (d : V) :
    smallProjection data r t (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem smallProjection_b_same
    (data : Certificates.PlusCaseAData G k s)
    (r t : Fin (k - 1)) :
    smallProjection data r t (Switching.Vertex.b r) = .a t := by
  simp [smallProjection]

@[simp]
private theorem smallProjection_b_of_ne
    (data : Certificates.PlusCaseAData G k s)
    (r t p : Fin (k - 1)) (hp : p ≠ r) :
    smallProjection data r t (Switching.Vertex.b p) = .b p := by
  simp [smallProjection, hp]

@[simp]
private theorem smallProjection_y
    (data : Certificates.PlusCaseAData G k s)
    (r t : Fin (k - 1)) (q : Fin (s - 1)) :
    smallProjection data r t
        (Switching.Vertex.y data.cert (some q)) =
      .core (data.cert.i q) := by
  simp [smallProjection]

private theorem noX_small_member_cases
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {r t : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K)
    (ht : t = r ∨ t ∈ P data)
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K → q = r ∨ q = t)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ∀ p, d ≠ data.cert.c p) ∨
    v = Switching.Vertex.b r ∨
    (t ≠ r ∧ t ∈ P data ∧ v = Switching.Vertex.b t) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q)) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · obtain ⟨d, heq, hdC, _⟩ := hcore
    exact Or.inl ⟨d, heq, hdC⟩
  · subst v
    exact False.elim
      (small_b_excludes_a2 data hKS hK hrSmall hr hv)
  · obtain ⟨q, rfl, hqQ⟩ := hb
    rcases hB q hv with hqr | hqt
    · subst q
      exact Or.inr (Or.inl rfl)
    · subst q
      by_cases htr : t = r
      · subst t
        exact Or.inr (Or.inl rfl)
      · have htP : t ∈ P data := ht.resolve_left htr
        exact Or.inr (Or.inr (Or.inl ⟨htr, htP, rfl⟩))
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · obtain ⟨q, heq, _, _⟩ := hy
    exact Or.inr (Or.inr (Or.inr ⟨q, heq⟩))

private theorem smallProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {r t : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K)
    (ht : t = r ∨ t ∈ P data)
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K → q = r ∨ q = t)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (smallProjection data r t u) (smallProjection data r t v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases noX_small_member_cases
      data hKS hK hnoX hrSmall hr ht hB hu with
      ⟨d, rfl, hdC⟩ | rfl | ⟨htr, htP, rfl⟩ | ⟨q, rfl⟩ <;>
    rcases noX_small_member_cases
      data hKS hK hnoX hrSmall hr ht hB hv with
      ⟨e, rfl, heC⟩ | rfl | ⟨htr', htP', rfl⟩ | ⟨p, rfl⟩
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    simpa only [smallProjection_core,
      specialLift_compl_adj_core_core] using hfirst
  ·
    rw [smallProjection_core, smallProjection_b_same,
      specialLift_compl_adj_core_a]
    exact (hdC t).symm
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [smallProjection_core,
      smallProjection_b_of_ne data r t t htr',
      specialLift_compl_adj_core_b]
    rw [specialLift_compl_adj_core_b] at hfirst
    exact hfirst
  ·
    have hd0 :
        (Switching.Vertex.lower (.core d) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    have hfirst := final_blue_lower_y_to_first data hd0 hfinal
    simpa only [smallProjection_core, smallProjection_y] using hfirst
  ·
    rw [smallProjection_b_same, smallProjection_core,
      specialLift_compl_adj_a_core]
    exact (heC t).symm
  · exact False.elim (huv.ne rfl)
  ·
    rw [smallProjection_b_same,
      smallProjection_b_of_ne data r t t htr',
      specialLift_compl_adj_a_b]
  ·
    rw [smallProjection_b_same, smallProjection_y,
      specialLift_compl_adj_a_core]
    exact data.cert.c_ne_i t p
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [smallProjection_b_of_ne data r t t htr,
      smallProjection_core,
      specialLift_compl_adj_b_core]
    rw [specialLift_compl_adj_b_core] at hfirst
    exact hfirst
  ·
    rw [smallProjection_b_of_ne data r t t htr,
      smallProjection_b_same,
      specialLift_compl_adj_b_a]
  · exact False.elim (huv.ne rfl)
  ·
    have ht0 : t ≠ c0Index data :=
      fun h ↦ c0_not_mem_P data (h ▸ htP)
    have hlower0 :
        (Switching.Vertex.lower (.b t) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have heq :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact ht0 heq
    have hfirst := final_blue_lower_y_to_first data hlower0 hfinal
    simpa only [smallProjection_b_of_ne data r t t htr,
      smallProjection_y] using hfirst
  ·
    have he0 :
        (Switching.Vertex.lower (.core e) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    have hfirst :=
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
    simpa only [smallProjection_y, smallProjection_core] using hfirst
  ·
    rw [smallProjection_y, smallProjection_b_same,
      specialLift_compl_adj_core_a]
    exact data.cert.c_ne_i t q
  ·
    have ht0 : t ≠ c0Index data :=
      fun h ↦ c0_not_mem_P data (h ▸ htP')
    have hlower0 :
        (Switching.Vertex.lower (.b t) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have heq :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact ht0 heq
    have hfirst :=
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data hlower0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
    simpa only [smallProjection_y,
      smallProjection_b_of_ne data r t t htr'] using hfirst
  ·
    have hqp : q ≠ p := by
      intro h
      subst p
      exact (Switching.finalGraph data.cert)ᶜ.loopless.irrefl _ hfinal
    simpa only [smallProjection_y,
      specialLift_compl_adj_core_core] using i_compl_adj data hqp

private theorem smallProjection_adjoins_i0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {r t : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K)
    (ht : t = r ∨ t ∈ P data)
    (hB : ∀ q : Fin (k - 1),
      Switching.Vertex.b q ∈ K → q = r ∨ q = t)
    {u : Switching.Vertex V k s} (hu : u ∈ K) :
    (specialLift G data.cert.c)ᶜ.Adj
      (smallProjection data r t u) (.core (i0 data)) := by
  rcases noX_small_member_cases
      data hKS hK hnoX hrSmall hr ht hB hu with
      ⟨d, rfl, hdC⟩ | rfl | ⟨htr, htP, rfl⟩ | ⟨q, rfl⟩
  ·
    have hdblue :
        ¬G.Adj (i0 data) d := by
      have hblue := hKS hu
      change ¬redToWA data (Switching.Vertex.core d) at hblue
      rw [redToWA_core] at hblue
      push Not at hblue
      exact hblue.2
    rw [smallProjection_core, specialLift_compl_adj_core_core,
      SimpleGraph.compl_adj]
    constructor
    · intro h
      subst d
      exact (small_b_excludes_i0 data hKS hK hrSmall hr) hu
    · simpa [G.adj_comm] using hdblue
  ·
    rw [smallProjection_b_same, specialLift_compl_adj_a_core]
    exact data.cert.c_ne_i t (i0Index data)
  ·
    rw [smallProjection_b_of_ne data r t t htr,
      specialLift_compl_adj_b_core]
    right
    rw [SimpleGraph.compl_adj]
    exact ⟨data.cert.c_ne_i t (i0Index data),
      (mem_P data t).1 htP⟩
  ·
    have hq0 : q ≠ i0Index data := by
      have hblue := hKS hu
      change ¬redToWA data
        (Switching.Vertex.y data.cert (some q)) at hblue
      rw [redToWA_y] at hblue
      push Not at hblue
      exact fun h ↦ hblue.2.1 (congrArg some h)
    rw [smallProjection_y, specialLift_compl_adj_core_core]
    exact i_compl_adj data hq0

private theorem noX_small_card_lt
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWA data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {r : Fin (k - 1)}
    (hrSmall : r = c0Index data ∨ r = c1Index data)
    (hr : Switching.Vertex.b r ∈ K) :
    K.card < s := by
  classical
  have hsmall :
      ∀ q : Fin (k - 1),
        (q = c0Index data ∨ q = c1Index data) →
        Switching.Vertex.b q ∈ K → q = r :=
    fun q hq hqK ↦
      small_b_index_unique data hKS hK hrSmall hq hr hqK
  by_cases hlarge :
      ∃ p ∈ P data, Switching.Vertex.b p ∈ K
  · obtain ⟨p, hpP, hpK⟩ := hlarge
    have hB :
        ∀ q : Fin (k - 1),
          Switching.Vertex.b q ∈ K → q = r ∨ q = p := by
      intro q hqK
      have hqBlue := hKS hqK
      change ¬redToWA data (Switching.Vertex.b q) at hqBlue
      rw [redToWA_b] at hqBlue
      rcases b_index_cases data hqBlue with hq0 | hq1 | hqP
      · exact Or.inl (hsmall q (Or.inl hq0) hqK)
      · exact Or.inl (hsmall q (Or.inr hq1) hqK)
      · exact Or.inr
          (large_b_index_unique data hKS hK hpP hqP hpK hqK)
    have hadj :
        ∀ {u v}, u ∈ K → v ∈ K →
          (BlueGraph data).Adj u v →
          (specialLift G data.cert.c)ᶜ.Adj
            (smallProjection data r p u)
            (smallProjection data r p v) :=
      fun {_ _} hu hv huv ↦
        smallProjection_maps_adj data hKS hK hnoX
          hrSmall hr (Or.inr hpP) hB hu hv huv
    have hadjoin :
        ∀ {u}, u ∈ K →
          (specialLift G data.cert.c)ᶜ.Adj
            (smallProjection data r p u) (.core (i0 data)) :=
      fun {_} hu ↦
        smallProjection_adjoins_i0 data hKS hK hnoX
          hrSmall hr (Or.inr hpP) hB hu
    have hfirst :
        IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
      specialLift_isRamseyFree G data.cert.c
        data.cert.c_isClique data.cert.five_le_k hG
    have hlt :
        K.card + 1 < s + 1 :=
      card_succ_lt_of_blue_projection data
        (smallProjection data r p) (.core (i0 data))
        hK hadj hadjoin hfirst.2
    omega
  ·
    push Not at hlarge
    have hB :
        ∀ q : Fin (k - 1),
          Switching.Vertex.b q ∈ K → q = r ∨ q = r := by
      intro q hqK
      have hqBlue := hKS hqK
      change ¬redToWA data (Switching.Vertex.b q) at hqBlue
      rw [redToWA_b] at hqBlue
      rcases b_index_cases data hqBlue with hq0 | hq1 | hqP
      · exact Or.inl (hsmall q (Or.inl hq0) hqK)
      · exact Or.inl (hsmall q (Or.inr hq1) hqK)
      · exact False.elim (hlarge q hqP hqK)
    have hadj :
        ∀ {u v}, u ∈ K → v ∈ K →
          (BlueGraph data).Adj u v →
          (specialLift G data.cert.c)ᶜ.Adj
            (smallProjection data r r u)
            (smallProjection data r r v) :=
      fun {_ _} hu hv huv ↦
        smallProjection_maps_adj data hKS hK hnoX
          hrSmall hr (Or.inl rfl) hB hu hv huv
    have hadjoin :
        ∀ {u}, u ∈ K →
          (specialLift G data.cert.c)ᶜ.Adj
            (smallProjection data r r u) (.core (i0 data)) :=
      fun {_} hu ↦
        smallProjection_adjoins_i0 data hKS hK hnoX
          hrSmall hr (Or.inl rfl) hB hu
    have hfirst :
        IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
      specialLift_isRamseyFree G data.cert.c
        data.cert.c_isClique data.cert.five_le_k hG
    have hlt :
        K.card + 1 < s + 1 :=
      card_succ_lt_of_blue_projection data
        (smallProjection data r r) (.core (i0 data))
        hK hadj hadjoin hfirst.2
    omega

/-- The blue neighborhood of the second Type A connector
contains no blue `K_s`. -/
theorem blueNeighborhoodA_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data)ᶜ.CliqueFreeOn
      {v | ¬redToWA data v} s := by
  classical
  intro K hKS hK
  have hlt : K.card < s := by
    by_cases hX :
        ∃ q : Fin (s - 1),
          Switching.Vertex.x data.cert (some q) ∈ K
    · obtain ⟨q, hq⟩ := hX
      by_cases hsecond :
          ∃ r : Fin (s - 1),
            Switching.Vertex.x data.cert (some r) ∈ K ∧ r ≠ q
      · obtain ⟨r, hr, hrq⟩ := hsecond
        exact blue_clique_card_lt_of_two_x
          data hG hKS hK.isClique hr hq hrq
      ·
        push Not at hsecond
        have honly :
            ∀ r : Fin (s - 1),
              Switching.Vertex.x data.cert (some r) ∈ K → r = q := by
          intro r hr
          exact hsecond r hr
        exact blue_clique_card_lt_of_one_x
          data hG hKS hK.isClique q hq honly
    ·
      push Not at hX
      by_cases hb0K : b0 data ∈ K
      · exact noX_small_card_lt data hG hKS hK.isClique hX
          (r := c0Index data) (Or.inl rfl) hb0K
      · by_cases hb1K : b1 data ∈ K
        · exact noX_small_card_lt data hG hKS hK.isClique hX
            (r := c1Index data) (Or.inr rfl) hb1K
        · by_cases hi0K : Switching.Vertex.core (i0 data) ∈ K
          · exact noX_noSmall_i0_card_lt
              data hG hKS hK.isClique hX hb0K hb1K hi0K
          · exact noX_noSmall_noI0_card_lt
              data hG hKS hK.isClique hX hb0K hb1K hi0K
  have hcard := hK.card_eq
  omega

end TypeA
end SecondConnector
end RamseyIncrement
