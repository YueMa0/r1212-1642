/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Projection
import RamseyIncrement.SecondConnector.TypeB.OldEdges

/-!
# Type B blue cliques through the second connector

This file formalizes the Type B blue-neighborhood analysis from the
strengthened second-connector argument.  The proof first reduces blue edges
inside the blue neighborhood of `w` to edges of the original first-connector
graph.  It then follows the three structural cases from the argument: at
least two ordinary `X` vertices, exactly one, and none.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private noncomputable abbrev BlueGraph
    (data : Certificates.PlusCaseBData G k s) :=
  (extraBOldGraph data)ᶜ

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

private abbrev b0
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.b
    (Certificates.c0Index data.cert.five_le_k)

private abbrev b1
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.b
    (Certificates.c1Index data.cert.five_le_k)

private abbrev b2
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.b (c2Index data)

/-! ## The exact blue neighborhood and reduction to the old graph -/

/-- Flat form of the blue neighborhood in (20B). -/
private theorem blue_member_cases
    (data : Certificates.PlusCaseBData G k s)
    {v : Switching.Vertex V k s}
    (hv : ¬redToWB data v) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      (∀ p, d ≠ data.cert.c p) ∧ ¬G.Adj (i2 data) d) ∨
    v = a2 data ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.b p ∧ p.val < 3) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.x data.cert (some q)) ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q) ∧
        q ≠ i2Index data) := by
  rcases vertex_six_block_cases data.cert v with
      h | h | h | h | h | h
  · obtain ⟨d, rfl⟩ := h
    rw [redToWB_core] at hv
    push Not at hv
    exact Or.inl ⟨d, rfl, hv.1, hv.2⟩
  · obtain ⟨p, rfl⟩ := h
    rw [redToWB_a] at hv
    push Not at hv
    subst p
    exact Or.inr (Or.inl rfl)
  · obtain ⟨p, rfl⟩ := h
    rw [redToWB_b] at hv
    exact Or.inr (Or.inr (Or.inl ⟨p, rfl, by omega⟩))
  · obtain ⟨r, rfl⟩ := h
    rw [redToWB_x] at hv
    cases r with
    | none => exact False.elim (hv rfl)
    | some q =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
  · obtain ⟨r, rfl⟩ := h
    rw [redToWB_y] at hv
    push Not at hv
    cases r with
    | none => exact False.elim (hv.1 rfl)
    | some q =>
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨q, rfl, fun hq ↦ hv.2 (congrArg some hq)⟩)))
  · subst v
    exact False.elim (hv (redToWB_z data))

/-- The only extra blue edge is `c₂x_*`; both endpoints are red to `w`.
Thus every blue edge inside `N_B(w)` was already blue in the
first-connector graph. -/
private theorem blue_adj_implies_final_blue
    (data : Certificates.PlusCaseBData G k s)
    {u v : Switching.Vertex V k s}
    (hu : ¬redToWB data u) (hv : ¬redToWB data v)
    (huv : (BlueGraph data).Adj u v) :
    (Switching.finalGraph data.cert)ᶜ.Adj u v := by
  by_contra hold
  have hchanged := classify_extraB_new_blue_edge data huv hold
  rcases hchanged with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact hu ((redToWB_core data (c2 data)).2 (Or.inl ⟨c2Index data, rfl⟩))
  · rcases h with ⟨rfl, rfl⟩
    exact hv ((redToWB_core data (c2 data)).2 (Or.inl ⟨c2Index data, rfl⟩))

/-! ## Public final-graph adjacency equations used in the counts -/

@[simp]
private theorem secondCertificate_some
    (data : Certificates.PlusCaseBData G k s)
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
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) (v : SpecialLiftVertex V k) :
    (Switching.preGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (.inl (.core v)) ↔
      Canonical.secondCertificateAt data.cert.toCertificates
        data.cert.five_le_k (some q) = v := by
  simp [Switching.preGraph, Switching.canonicalGraph, Canonical.graph,
    Switching.Vertex.x, Canonical.secondCertificate_apply,
    Switching.redJoinedClone]
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

private theorem final_blue_adj_x_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (q r : Fin (s - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.x data.cert (some r)) ↔ q ≠ r := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.x]

private theorem final_blue_adj_x_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (q r : Fin (s - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.y data.cert (some r)) ↔ q ≠ r := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.x, Switching.Vertex.y,
    Canonical.secondCertificateAt]

private theorem final_blue_adj_x_core_iff
    (data : Certificates.PlusCaseBData G k s)
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
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.a p) ↔
      q ∈ data.cert.E ∧ p = Certificates.c0Index data.cert.five_le_k := by
  have hpre := pre_blue_adj_x_lower_iff data q
    (SpecialLiftVertex.a p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [Switching.finalGraph, Switching.removedRedGraph,
    Switching.removedRedRel, Switching.addedRedGraph,
    Switching.addedRedRel, hpre, Switching.Vertex.x,
    Switching.Vertex.a, Switching.Vertex.c0,
    and_comm, and_left_comm, and_assoc]

private theorem final_blue_adj_x_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.x data.cert (some q))
        (Switching.Vertex.b p) ↔
      q = Switching.Vertex.i1 data.cert ∧
        p = Certificates.c0Index data.cert.five_le_k := by
  have hpre := pre_blue_adj_x_lower_iff data q
    (SpecialLiftVertex.b p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [Switching.finalGraph, Switching.removedRedGraph,
    Switching.removedRedRel, Switching.addedRedGraph,
    Switching.addedRedRel, hpre, Switching.Vertex.x,
    Switching.Vertex.b, Switching.Vertex.c0,
    Switching.Vertex.i1, and_comm, and_left_comm, and_assoc]

private theorem final_blue_adj_y_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (q r : Fin (s - 1)) :
    (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.y data.cert (some r)) ↔
      q ≠ r ∧
        (SameBPart (k := s + 1)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                data.cert.five_le_s)).symm (some q))
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                data.cert.five_le_s)).symm (some r)) ∨
          (q = Switching.Vertex.i1 data.cert ∧
            r ∈ data.cert.E ∧ 2 ≤ r.val) ∨
          (r = Switching.Vertex.i1 data.cert ∧
            q ∈ data.cert.E ∧ 2 ≤ q.val)) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.y, Switching.Vertex.i1,
    Switching.redJoinedClone]
  tauto

/-! ## At least two `X` vertices -/

/-- Index projection used once the two-`X` classifier has excluded all
blocks except ordinary `X` and ordinary `Y`. -/
private def xyIndex
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → Fin (s - 1)
  | .inl (.a q) =>
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s)) q |>.getD
        (i2Index data)
  | .inl (.b q) =>
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s)) q |>.getD
        (i2Index data)
  | _ => i2Index data

@[simp]
private theorem xyIndex_x
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    xyIndex data (Switching.Vertex.x data.cert (some q)) = q := by
  simp [xyIndex, Switching.Vertex.x]

@[simp]
private theorem xyIndex_y
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    xyIndex data (Switching.Vertex.y data.cert (some q)) = q := by
  simp [xyIndex, Switching.Vertex.y]

/-- Two distinct ordinary `X` vertices exclude every old block.  The
remaining `X` and `Y` vertices inject into the `s-1` ordinary indices,
with the red diagonal preventing an `X/Y` collision. -/
private theorem blue_clique_card_lt_of_two_x
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    {q r : Fin (s - 1)}
    (hqx : Switching.Vertex.x data.cert (some q) ∈ K)
    (hrx : Switching.Vertex.x data.cert (some r) ∈ K)
    (hqr : q ≠ r) :
    K.card < s := by
  classical
  have hqblue : ¬redToWB data
      (Switching.Vertex.x data.cert (some q)) := hKS hqx
  have hrblue : ¬redToWB data
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
      exact False.elim (hqr (data.cert.i.injective (hqd.symm.trans hrd)))
    · subst v
      have hqa := (final_blue_adj_x_a_iff data q (c2Index data)).1
        (blue_adj_implies_final_blue data hqblue hvblue
          (hK hqx hv (by simp [a2])))
      have hval := congrArg Fin.val hqa.2
      simp [c2Index, Certificates.c2Index,
        Certificates.c0Index] at hval
    · obtain ⟨p, rfl, hp3⟩ := hb
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
    · have hpt : p = t := by
        simpa [hp, ht] using huv
      subst t
      apply Subtype.ext
      exact hp.trans ht.symm
    · have hpt : p = t := by
        simpa [hp, ht] using huv
      subst t
      have hne : (u : Switching.Vertex V k s) ≠ v := by
        rw [hp, ht]
        simp [Switching.Vertex.x, Switching.Vertex.y]
      have hadj := hK u.2 v.2 hne
      have hfinal := blue_adj_implies_final_blue data
        (hKS u.2) (hKS v.2) hadj
      rw [hp, ht] at hfinal
      exact False.elim ((final_blue_adj_x_y_iff data p p).1 hfinal rfl)
    · have hpt : p = t := by
        simpa [hp, ht] using huv
      subst t
      have hne : (u : Switching.Vertex V k s) ≠ v := by
        rw [hp, ht]
        simp [Switching.Vertex.x, Switching.Vertex.y]
      have hadj := hK u.2 v.2 hne
      have hfinal := blue_adj_implies_final_blue data
        (hKS u.2) (hKS v.2) hadj
      rw [hp, ht] at hfinal
      exact False.elim ((final_blue_adj_x_y_iff data p p).1
        ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal) rfl)
    · have hpt : p = t := by
        simpa [hp, ht] using huv
      subst t
      apply Subtype.ext
      exact hp.trans ht.symm
  have hcard : K.card ≤ s - 1 := by
    rw [← Fintype.card_coe]
    simpa using Fintype.card_le_of_injective
      (fun v : {v // v ∈ K} ↦ xyIndex data v.1) hinj
  have hs := data.cert.five_le_s
  omega

/-! ## Bounds for ordinary `Y` cliques -/

private abbrev i0Index
    (data : Certificates.PlusCaseBData G k s) : Fin (s - 1) :=
  Certificates.i0Index' data.cert.five_le_s

private abbrev i1Index
    (data : Certificates.PlusCaseBData G k s) : Fin (s - 1) :=
  Switching.Vertex.i1 data.cert

/-- The ordinary `Y` vertices indexed by a finite set. -/
private def ySet
    (data : Certificates.PlusCaseBData G k s)
    (Q : Finset (Fin (s - 1))) :
    Finset (Switching.Vertex V k s) :=
  Q.map
    ⟨fun q ↦ Switching.Vertex.y data.cert (some q),
      fun _ _ h ↦ Option.some.inj (vertex_y_injective data.cert h)⟩

@[simp]
private theorem mem_ySet
    (data : Certificates.PlusCaseBData G k s)
    (Q : Finset (Fin (s - 1))) (q : Fin (s - 1)) :
    Switching.Vertex.y data.cert (some q) ∈ ySet data Q ↔ q ∈ Q := by
  simp [ySet]

@[simp]
private theorem card_ySet
    (data : Certificates.PlusCaseBData G k s)
    (Q : Finset (Fin (s - 1))) :
    (ySet data Q).card = Q.card := by
  simp [ySet]

/-- The actual ordinary `Y` indices occurring in a finite set. -/
private noncomputable def yIndices
    (data : Certificates.PlusCaseBData G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Finset (Fin (s - 1)) := by
  classical
  exact Finset.univ.filter fun q ↦
    Switching.Vertex.y data.cert (some q) ∈ K

@[simp]
private theorem mem_yIndices
    (data : Certificates.PlusCaseBData G k s)
    (K : Finset (Switching.Vertex V k s)) (q : Fin (s - 1)) :
    q ∈ yIndices data K ↔
      Switching.Vertex.y data.cert (some q) ∈ K := by
  simp [yIndices]

private theorem i2_not_mem_yIndices
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v}) :
    i2Index data ∉ yIndices data K := by
  rw [mem_yIndices]
  intro hy
  exact hKS hy ((redToWB_y data (some (i2Index data))).2
    (Or.inr rfl))

private theorem yIndices_pair_blue
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    {q r : Fin (s - 1)}
    (hq : q ∈ yIndices data K) (hr : r ∈ yIndices data K)
    (hqr : q ≠ r) :
    (Switching.finalGraph data.cert)ᶜ.Adj
      (Switching.Vertex.y data.cert (some q))
      (Switching.Vertex.y data.cert (some r)) := by
  rw [mem_yIndices] at hq hr
  exact blue_adj_implies_final_blue data (hKS hq) (hKS hr)
    (hK hq hr (fun h ↦ hqr
      (Option.some.inj (vertex_y_injective data.cert h))))

private theorem small_index_eq_i0_or_i1
    (data : Certificates.PlusCaseBData G k s)
    {q : Fin (s - 1)} (hq : q.val < 2) :
    q = i0Index data ∨ q = i1Index data := by
  have hq0 : q.val = 0 ∨ q.val = 1 := by omega
  rcases hq0 with hq0 | hq1
  · left
    apply Fin.ext
    simpa [i0Index, Certificates.i0Index'] using hq0
  · right
    apply Fin.ext
    simpa [i1Index, Switching.Vertex.i1,
      Certificates.i1Index'] using hq1

/-- Any Type B blue clique of ordinary `Y` vertices avoiding index 2 has
order at most `max 2 (s-4)`.  A mixed-part clique is exactly `y₁`
together with large exceptional indices, bounded by (7a). -/
private theorem yIndexClique_card_le
    (data : Certificates.PlusCaseBData G k s)
    (Q : Finset (Fin (s - 1)))
    (h2 : i2Index data ∉ Q)
    (hblue : ∀ {q r}, q ∈ Q → r ∈ Q → q ≠ r →
      (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.y data.cert (some r))) :
    Q.card ≤ max 2 (s - 4) := by
  classical
  by_cases hallSmall : ∀ q ∈ Q, q.val < 2
  · have hsub : Q ⊆ {i0Index data, i1Index data} := by
      intro q hq
      rcases small_index_eq_i0_or_i1 data (hallSmall q hq) with h | h
      · simp [h]
      · simp [h]
    have hc := Finset.card_le_card hsub
    have hpair : ({i0Index data, i1Index data} :
        Finset (Fin (s - 1))).card ≤ 2 := by
      have hfirst := Finset.card_insert_le
        (i0Index data) ({i1Index data} : Finset (Fin (s - 1)))
      simp at hfirst
      omega
    have hmax : 2 ≤ max 2 (s - 4) := Nat.le_max_left _ _
    omega
  · push Not at hallSmall
    obtain ⟨q, hqQ, hqLarge⟩ := hallSmall
    have hq2 : 2 ≤ q.val := by omega
    by_cases hallLarge : ∀ r ∈ Q, 2 ≤ r.val
    · have hsub : Q ⊆ data.cert.largeIndices.erase (i2Index data) := by
        intro r hr
        rw [Finset.mem_erase]
        exact ⟨fun h ↦ h2 (h ▸ hr),
          (data.cert.mem_largeIndices_iff r).2 (hallLarge r hr)⟩
      have hc := Finset.card_le_card hsub
      have hi2large : i2Index data ∈ data.cert.largeIndices :=
        (data.cert.mem_largeIndices_iff _).2 (by
          simp [i2Index, Certificates.i2Index'])
      rw [Finset.card_erase_of_mem hi2large,
        data.cert.card_largeIndices] at hc
      have hs := data.cert.five_le_s
      exact le_trans (by omega) (Nat.le_max_right _ _)
    · push Not at hallLarge
      obtain ⟨r, hrQ, hrSmall⟩ := hallLarge
      have hrLt : r.val < 2 := by omega
      have hrq : r ≠ q := by
        intro h
        subst q
        omega
      have hrqBlue := (final_blue_adj_y_y_iff data r q).1
        (hblue hrQ hqQ hrq)
      have hr1 : r = i1Index data := by
        rcases hrqBlue.2 with hpart | hswitch | hswitch
        · have hparts :
              (r.val < 2 ∧ q.val < 2) ∨
                (2 ≤ r.val ∧ 2 ≤ q.val) := by
            simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
          omega
        · exact hswitch.1
        · have hq1 := congrArg Fin.val hswitch.1
          simp [i1Index, Switching.Vertex.i1,
            Certificates.i1Index'] at hq1
          omega
      have hsub : Q ⊆ insert (i1Index data) data.cert.ELarge := by
        intro t ht
        by_cases htSmall : t.val < 2
        · by_cases htq : t = q
          · subst t
            omega
          · have htqBlue := (final_blue_adj_y_y_iff data t q).1
              (hblue ht hqQ htq)
            rcases htqBlue.2 with hpart | hswitch | hswitch
            · have hparts :
                  (t.val < 2 ∧ q.val < 2) ∨
                    (2 ≤ t.val ∧ 2 ≤ q.val) := by
                simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
              omega
            · simp [hswitch.1]
            · have hq1 := congrArg Fin.val hswitch.1
              simp [i1Index, Switching.Vertex.i1,
                Certificates.i1Index'] at hq1
              omega
        · have htLarge : 2 ≤ t.val := by omega
          by_cases htr : t = r
          · subst t
            omega
          · have hrtBlue := (final_blue_adj_y_y_iff data r t).1
              (hblue hrQ ht (Ne.symm htr))
            rcases hrtBlue.2 with hpart | hswitch | hswitch
            · have hparts :
                  (r.val < 2 ∧ t.val < 2) ∨
                    (2 ≤ r.val ∧ 2 ≤ t.val) := by
                simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
              omega
            · exact Finset.mem_insert_of_mem
                ((data.cert.mem_ELarge t).2
                  ⟨hswitch.2.1, htLarge⟩)
            · have ht1 := congrArg Fin.val hswitch.1
              simp [i1Index, Switching.Vertex.i1,
                Certificates.i1Index'] at ht1
              omega
      have hc := Finset.card_le_card hsub
      have hins := Finset.card_insert_le (i1Index data) data.cert.ELarge
      have hE := data.cert.caseB_card_ELarge_le data.baseB
      have hk := data.cert.five_le_k
      have hs := data.cert.five_le_s
      have hright : s - 4 ≤ max 2 (s - 4) := Nat.le_max_right _ _
      omega

/-- If index 1 is absent, the exceptional cross-part edges disappear and
the sharper `s-4` bound holds. -/
private theorem yIndexClique_card_le_of_no_i1
    (data : Certificates.PlusCaseBData G k s)
    (Q : Finset (Fin (s - 1)))
    (h2 : i2Index data ∉ Q)
    (h1 : i1Index data ∉ Q)
    (hblue : ∀ {q r}, q ∈ Q → r ∈ Q → q ≠ r →
      (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.y data.cert (some r))) :
    Q.card ≤ s - 4 := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨q, hqQ⟩ := hQ
    by_cases hqSmall : q.val < 2
    · have hq0 : q = i0Index data := by
        rcases small_index_eq_i0_or_i1 data hqSmall with h | h
        · exact h
        · exact False.elim (h1 (h ▸ hqQ))
      have hsub : Q ⊆ {i0Index data} := by
        intro r hr
        by_cases hrq : r = q
        · simp [hrq, hq0]
        · have hqr := (final_blue_adj_y_y_iff data q r).1
              (hblue hqQ hr (Ne.symm hrq))
          rcases hqr.2 with hpart | hswitch | hswitch
          · have hparts :
                (q.val < 2 ∧ r.val < 2) ∨
                  (2 ≤ q.val ∧ 2 ≤ r.val) := by
              simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
            have hrSmall : r.val < 2 := by omega
            rcases small_index_eq_i0_or_i1 data hrSmall with hr0 | hr1
            · simp [hr0]
            · exact False.elim (h1 (hr1 ▸ hr))
          · exact False.elim (h1 (by
              simpa [i1Index] using (hswitch.1 ▸ hqQ)))
          · exact False.elim (h1 (by
              simpa [i1Index] using (hswitch.1 ▸ hr)))
      have hc := Finset.card_le_card hsub
      have hs := data.cert.five_le_s
      simp at hc
      omega
    · have hqLarge : 2 ≤ q.val := by omega
      have hsub : Q ⊆ data.cert.largeIndices.erase (i2Index data) := by
        intro r hr
        have hrLarge : 2 ≤ r.val := by
          by_contra hrnot
          have hrSmall : r.val < 2 := by omega
          by_cases hrq : r = q
          · subst r
            omega
          · have hrqBlue := (final_blue_adj_y_y_iff data r q).1
                (hblue hr hqQ hrq)
            rcases hrqBlue.2 with hpart | hswitch | hswitch
            · have hparts :
                  (r.val < 2 ∧ q.val < 2) ∨
                    (2 ≤ r.val ∧ 2 ≤ q.val) := by
                simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
              omega
            · exact h1 (by
                simpa [i1Index] using (hswitch.1 ▸ hr))
            · have hq1 := congrArg Fin.val hswitch.1
              simp [i1Index, Switching.Vertex.i1,
                Certificates.i1Index'] at hq1
              omega
        rw [Finset.mem_erase]
        exact ⟨fun h ↦ h2 (h ▸ hr),
          (data.cert.mem_largeIndices_iff r).2 hrLarge⟩
      have hc := Finset.card_le_card hsub
      have hi2large : i2Index data ∈ data.cert.largeIndices :=
        (data.cert.mem_largeIndices_iff _).2 (by
          simp [i2Index, Certificates.i2Index'])
      rw [Finset.card_erase_of_mem hi2large,
        data.cert.card_largeIndices] at hc
      exact hc
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hQ]

/-! ## Exactly one `X` vertex -/

/-- The exactly-one-`X` count.  The only possible old
vertex is the matched `i_r`, except at `r=1`, where `b₀` may also occur.
The preceding `Y` lemmas supply the sharp exceptional-edge bound. -/
private theorem blue_clique_card_lt_of_one_x
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (r : Fin (s - 1))
    (hxr : Switching.Vertex.x data.cert (some r) ∈ K)
    (honly : ∀ t : Fin (s - 1),
      Switching.Vertex.x data.cert (some t) ∈ K → t = r) :
    K.card < s := by
  classical
  let Q := yIndices data K
  have hxblue : ¬redToWB data
      (Switching.Vertex.x data.cert (some r)) := hKS hxr
  have h2 : i2Index data ∉ Q :=
    i2_not_mem_yIndices data hKS
  have hYblue : ∀ {q t}, q ∈ Q → t ∈ Q → q ≠ t →
      (Switching.finalGraph data.cert)ᶜ.Adj
        (Switching.Vertex.y data.cert (some q))
        (Switching.Vertex.y data.cert (some t)) :=
    fun {_ _} hq ht hqt ↦
      yIndices_pair_blue data hKS hK hq ht hqt
  have hdiag : r ∉ Q := by
    rw [mem_yIndices]
    intro hyr
    have hfinal := blue_adj_implies_final_blue data hxblue (hKS hyr)
      (hK hxr hyr (by simp [Switching.Vertex.x, Switching.Vertex.y]))
    exact (final_blue_adj_x_y_iff data r r).1 hfinal rfl
  by_cases hr1 : r = i1Index data
  · have h1 : i1Index data ∉ Q := by simpa [hr1] using hdiag
    have hQcard : Q.card ≤ s - 4 :=
      yIndexClique_card_le_of_no_i1 data Q h2 h1 hYblue
    have hsub :
        K ⊆ insert (Switching.Vertex.x data.cert (some r))
          (insert (Switching.Vertex.core (data.cert.i r))
            (insert (b0 data) (ySet data Q))) := by
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
        have hxa := (final_blue_adj_x_a_iff data r (c2Index data)).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp [a2])))
        have hval := congrArg Fin.val hxa.2
        simp [c2Index, Certificates.c2Index,
          Certificates.c0Index] at hval
      · obtain ⟨p, rfl, hp3⟩ := hb
        have hxb := (final_blue_adj_x_b_iff data r p).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        have hp0 := hxb.2
        subst p
        simp [b0]
      · obtain ⟨t, rfl⟩ := hx
        have ht := honly t hv
        subst t
        simp
      · obtain ⟨q, rfl, hq2⟩ := hy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              ((mem_ySet data Q q).2 ((mem_yIndices data K q).2 hv))))
    have hc := Finset.card_le_card hsub
    have hA := Finset.card_insert_le
      (Switching.Vertex.x data.cert (some r))
      (insert (Switching.Vertex.core (data.cert.i r))
        (insert (b0 data) (ySet data Q)))
    have hB := Finset.card_insert_le
      (Switching.Vertex.core (data.cert.i r))
      (insert (b0 data) (ySet data Q))
    have hC := Finset.card_insert_le (b0 data) (ySet data Q)
    rw [card_ySet] at hC
    have hs := data.cert.five_le_s
    omega
  · have hQcard : Q.card ≤ max 2 (s - 4) :=
      yIndexClique_card_le data Q h2 hYblue
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
        have hxa := (final_blue_adj_x_a_iff data r (c2Index data)).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp [a2])))
        have hval := congrArg Fin.val hxa.2
        simp [c2Index, Certificates.c2Index,
          Certificates.c0Index] at hval
      · obtain ⟨p, rfl, hp3⟩ := hb
        have hxb := (final_blue_adj_x_b_iff data r p).1
          (blue_adj_implies_final_blue data hxblue hvblue
            (hK hxr hv (by simp)))
        exact False.elim (hr1 hxb.1)
      · obtain ⟨t, rfl⟩ := hx
        have ht := honly t hv
        subst t
        simp
      · obtain ⟨q, rfl, hq2⟩ := hy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem
            ((mem_ySet data Q q).2 ((mem_yIndices data K q).2 hv)))
    have hc := Finset.card_le_card hsub
    have hA := Finset.card_insert_le
      (Switching.Vertex.x data.cert (some r))
      (insert (Switching.Vertex.core (data.cert.i r)) (ySet data Q))
    have hB := Finset.card_insert_le
      (Switching.Vertex.core (data.cert.i r)) (ySet data Q)
    rw [card_ySet] at hB
    have hs := data.cert.five_le_s
    by_cases hmax : s - 4 ≤ 2
    · rw [Nat.max_eq_left hmax] at hQcard
      omega
    · have hmax' : 2 ≤ s - 4 := by omega
      rw [Nat.max_eq_right hmax'] at hQcard
      omega

/-! ## No `X` vertices: projection to the first lift -/

/-- Project ordinary `Y_q` to `i_q` and otherwise forget the outer lift
and clone tags.  On a no-`X` blue clique in `N_B(w)`, this is the basic
projection into the first lift `L`. -/
private def oldProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core v) => v
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some r => .core (data.cert.i r)
      | none => .core (i2 data)
  | _ => .core (i2 data)

@[simp]
private theorem oldProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    oldProjection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem oldProjection_a
    (data : Certificates.PlusCaseBData G k s) (p : Fin (k - 1)) :
    oldProjection data (Switching.Vertex.a p) = .a p :=
  rfl

@[simp]
private theorem oldProjection_b
    (data : Certificates.PlusCaseBData G k s) (p : Fin (k - 1)) :
    oldProjection data (Switching.Vertex.b p) = .b p :=
  rfl

@[simp]
private theorem oldProjection_y
    (data : Certificates.PlusCaseBData G k s) (q : Fin (s - 1)) :
    oldProjection data (Switching.Vertex.y data.cert (some q)) =
      .core (data.cert.i q) := by
  simp [oldProjection, Switching.Vertex.y]

/-- The projection is literally the identity on the lower copy of the
first lift. -/
@[simp]
private theorem oldProjection_lower
    (data : Certificates.PlusCaseBData G k s)
    (d : SpecialLiftVertex V k) :
    oldProjection data (Switching.Vertex.lower d) = d := by
  cases d <;> rfl

/-- A final-blue edge between two lower vertices was already blue in the
first lift.  None of the first-stage blue switches has two lower
endpoints. -/
private theorem final_blue_lower_lower_to_first
    (data : Certificates.PlusCaseBData G k s)
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
blue edge of the first lift.  The excluded vertex is exactly the lower
endpoint of the first-stage switches that can invalidate this statement. -/
private theorem final_blue_lower_y_to_first
    (data : Certificates.PlusCaseBData G k s)
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
    simpa [hrem.2]
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

/-- Distinct ordinary second-certificate vertices lie in the certified
blue clique `I`. -/
private theorem i_compl_adj
    (data : Certificates.PlusCaseBData G k s)
    {q r : Fin (s - 1)} (hqr : q ≠ r) :
    Gᶜ.Adj (data.cert.i q) (data.cert.i r) :=
  data.cert.i_compl_adj hqr

/-- With ordinary `X` vertices excluded, every blue neighbor of `w` is
either a lower vertex or an ordinary `Y` vertex. -/
private theorem noX_member_lower_or_y
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
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
  · obtain ⟨q, rfl, _⟩ := hy
    exact Or.inr ⟨q, rfl⟩

/-- Pairwise form of the basic projection lemma. -/
private theorem oldProjection_maps_adj_of_ne_b0
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (hu0 : u ≠ b0 data) (hv0 : v ≠ b0 data)
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
          Switching.Vertex V k s) ≠ b0 data := hu0
    simpa only [oldProjection_lower, oldProjection_y] using
      final_blue_lower_y_to_first data hd0 hfinal
  ·
    have he0 :
        (Switching.Vertex.lower e :
          Switching.Vertex V k s) ≠ b0 data := hv0
    simpa only [oldProjection_lower, oldProjection_y] using
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
  ·
    have hqr :=
      (final_blue_adj_y_y_iff data q r).1 hfinal |>.1
    simpa only [oldProjection_y, specialLift_compl_adj_core_core] using
      i_compl_adj data hqr

/-- On a no-`X` clique which omits `b₀`, the basic projection preserves
all blue edges.  In particular, the exceptional cross-part `Y` edges map
inside the certified blue clique `I`. -/
private theorem oldProjection_maps_adj_without_b0
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0 : b0 data ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (oldProjection data u) (oldProjection data v) := by
  apply oldProjection_maps_adj_of_ne_b0
      data hKS hnoX hu hv
  · exact fun h ↦ hb0 (h ▸ hu)
  · exact fun h ↦ hb0 (h ▸ hv)
  · exact huv

/-! ## Cardinal tools and the five restricted no-`X` certificates -/

/-- An adjacency-preserving projection of a finite clique is injective on
that clique, since identifying two distinct source vertices would create a
loop in the target. -/
private theorem card_lt_of_blue_projection
    {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (f : Switching.Vertex V k s → W)
    (hK : (BlueGraph data).IsClique K)
    (hadj : ∀ {u v}, u ∈ K → v ∈ K →
      (BlueGraph data).Adj u v → H.Adj (f u) (f v))
    (hfree : H.CliqueFree n) :
    K.card < n := by
  classical
  let e : {v // v ∈ K} ↪ W :=
    { toFun := fun v ↦ f v.1
      inj' := by
        intro u v huv
        apply Subtype.ext
        by_contra hne
        have hedge := hadj u.2 v.2 (hK u.2 v.2 hne)
        change f u.1 = f v.1 at huv
        rw [huv] at hedge
        exact H.loopless.irrefl _ hedge }
  have hclique :
      ∀ u v : {v // v ∈ K}, u ≠ v →
        H.Adj (e u) (e v) := by
    intro u v huv
    apply hadj u.2 v.2
    apply hK u.2 v.2
    intro heq
    exact huv (Subtype.ext heq)
  have hlt := card_lt_of_cliqueFree_of_embedding hfree e hclique
  simpa using hlt

/-- Version of the preceding projection argument in which one fresh
target vertex is adjoined. -/
private theorem card_succ_lt_of_blue_projection
    {W : Type*} {H : SimpleGraph W} {n : ℕ}
    (data : Certificates.PlusCaseBData G k s)
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
    ·
      apply hadj u.2 v.2
      apply hK u.2 v.2
      intro heq
      exact huv (congrArg Sum.inl (Subtype.ext heq))
    · exact hadjoin u.2
    · exact H.adj_symm (hadjoin v.2)
    · exact False.elim
        (huv (congrArg Sum.inr (Subsingleton.elim u v)))
  have hlt := card_lt_of_cliqueFree_of_embedding hfree e hclique
  simpa using hlt

/-- The three indices below `3` are exactly `0,1,2`. -/
private theorem index_lt_three_cases
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) (hp : p.val < 3) :
    p = Certificates.c0Index data.cert.five_le_k ∨
    p = Certificates.c1Index data.cert.five_le_k ∨
    p = c2Index data := by
  have hpv : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 := by omega
  rcases hpv with hpv | hpv | hpv
  · left
    apply Fin.ext
    simpa [Certificates.c0Index] using hpv
  · right
    left
    apply Fin.ext
    simpa [Certificates.c1Index] using hpv
  · right
    right
    apply Fin.ext
    simpa [c2Index, Certificates.c2Index] using hpv

/-- In Case B the matched pair `c₂i₂` is blue. -/
private theorem c2_compl_adj_i2
    (data : Certificates.PlusCaseBData G k s) :
    Gᶜ.Adj (c2 data) (i2 data) := by
  rw [SimpleGraph.compl_adj]
  constructor
  · exact data.cert.c_ne_i (c2Index data) (i2Index data)
  ·
    have hblue :=
      data.cert.caseB_not_adj_matched data.baseB (c2Index data)
    rw [Certificates.castIndex_c2'
      data.cert.five_le_k data.cert.five_le_s
      data.baseB.k_le_s] at hblue
    exact hblue

/-- Every nonmatched Case B certificate vertex is red to `i₂`. -/
private theorem c_adj_i2_of_ne_c2
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) (hp : p ≠ c2Index data) :
    G.Adj (data.cert.c p) (i2 data) := by
  have hred := data.cert.caseB_adj_of_ne data.baseB hp
  rw [Certificates.castIndex_c2'
    data.cert.five_le_k data.cert.five_le_s
    data.baseB.k_le_s] at hred
  exact hred

/-- The additional Type B edit makes `i₂a₂` red. -/
private theorem not_blue_i2_a2
    (data : Certificates.PlusCaseBData G k s) :
    ¬(BlueGraph data).Adj
      (Switching.Vertex.core (i2 data)) (a2 data) := by
  intro hblue
  have hadd :
      (extraBAddedRedGraph data).Adj
        (Switching.Vertex.core (i2 data)) (a2 data) := by
    rw [extraBAddedRedGraph_adj_iff]
    exact Or.inl ⟨rfl, rfl⟩
  have hred := extraBOldGraph_adj_of_added data hadd
  exact ((SimpleGraph.compl_adj _ _ _).1 hblue).2 hred

/-- No small `B` vertex and no `i₂`: retain the lower vertices, send
`y_q` to `i_q`, and adjoin `i₂` in the first lift. -/
private theorem noX_noSmall_noI2_card_lt
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi2K : Switching.Vertex.core (i2 data) ∉ K) :
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
          (oldProjection data u) (.core (i2 data)) := by
    intro u hu
    rcases blue_member_cases data (hKS hu) with
        hcore | ha | hb | hx | hy
    · obtain ⟨d, rfl, _, hdblue⟩ := hcore
      rw [oldProjection_core, specialLift_compl_adj_core_core,
        SimpleGraph.compl_adj]
      constructor
      · intro hdi
        subst d
        exact hi2K hu
      · simpa [G.adj_comm] using hdblue
    · subst u
      rw [oldProjection_a, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i (c2Index data) (i2Index data)
    · obtain ⟨p, rfl, hp3⟩ := hb
      rcases index_lt_three_cases data p hp3 with hp0 | hp1 | hp2
      · subst p
        exact False.elim (hb0K hu)
      · subst p
        exact False.elim (hb1K hu)
      · subst p
        rw [oldProjection_b, specialLift_compl_adj_b_core]
        exact Or.inr (c2_compl_adj_i2 data)
    · obtain ⟨q, rfl⟩ := hx
      exact False.elim (hnoX q hu)
    · obtain ⟨q, rfl, hq2⟩ := hy
      rw [oldProjection_y, specialLift_compl_adj_core_core]
      exact i_compl_adj data hq2
  have hfirst :
      IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  have hlt :
      K.card + 1 < s + 1 :=
    card_succ_lt_of_blue_projection data
      (oldProjection data) (.core (i2 data))
      hK hadj hadjoin hfirst.2
  omega

/-- Projection used when `i₂` itself occurs: core vertices are retained,
ordinary `Y_q` goes to `i_q`, and any surviving `b₂` goes to `c₂`. -/
private def baseProjection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → V
  | .inl (.core (.core d)) => d
  | .inl (.core (.b p)) => data.cert.c p
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some r => data.cert.i r
      | none => i2 data
  | _ => i2 data

@[simp]
private theorem baseProjection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    baseProjection data (Switching.Vertex.core d) = d :=
  rfl

@[simp]
private theorem baseProjection_b
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    baseProjection data (Switching.Vertex.b p) = data.cert.c p :=
  rfl

@[simp]
private theorem baseProjection_y
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    baseProjection data
        (Switching.Vertex.y data.cert (some q)) = data.cert.i q := by
  simp [baseProjection, Switching.Vertex.y]

/-- With `i₂` present and the two small `B` vertices absent, the only
possible vertices are core vertices outside `C`, `b₂`, and ordinary
`Y` vertices.  The new red edge `i₂a₂` excludes `a₂`. -/
private theorem noX_noSmall_i2_member_cases
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi2K : Switching.Vertex.core (i2 data) ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ∀ p, d ≠ data.cert.c p) ∨
    v = b2 data ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q)) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · obtain ⟨d, heq, hdC, _⟩ := hcore
    exact Or.inl ⟨d, heq, hdC⟩
  · subst v
    have hblue := hK hi2K hv (by simp [a2])
    exact False.elim (not_blue_i2_a2 data hblue)
  · obtain ⟨p, rfl, hp3⟩ := hb
    rcases index_lt_three_cases data p hp3 with hp0 | hp1 | hp2
    · subst p
      exact False.elim (hb0K hv)
    · subst p
      exact False.elim (hb1K hv)
    · subst p
      exact Or.inr (Or.inl rfl)
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · obtain ⟨q, heq, _⟩ := hy
    exact Or.inr (Or.inr ⟨q, heq⟩)

/-- The restricted `i₂`-present projection preserves all blue edges. -/
private theorem baseProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi2K : Switching.Vertex.core (i2 data) ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    Gᶜ.Adj (baseProjection data u) (baseProjection data v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases noX_noSmall_i2_member_cases
      data hKS hK hnoX hb0K hb1K hi2K hu with
      ⟨d, rfl, hdC⟩ | rfl | ⟨q, rfl⟩ <;>
    rcases noX_noSmall_i2_member_cases
      data hKS hK hnoX hb0K hb1K hi2K hv with
      ⟨e, rfl, heC⟩ | rfl | ⟨r, rfl⟩
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    simpa only [baseProjection_core,
      specialLift_compl_adj_core_core] using hfirst
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_core_b] at hfirst
    rcases hfirst with hdc | hdc
    · exact False.elim (hdC (c2Index data) hdc)
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
    · exact False.elim (heC (c2Index data) hec)
    · simpa only [baseProjection_b, baseProjection_core] using hec
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    exact False.elim
      ((specialLift G data.cert.c)ᶜ.loopless.irrefl _ hfirst)
  ·
    have h20 :
        (Switching.Vertex.lower (.b (c2Index data)) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hp :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact (Switching.Vertex.c0_ne_c2 data.cert).symm hp
    have hfirst := final_blue_lower_y_to_first data h20 hfinal
    rw [specialLift_compl_adj_b_core] at hfirst
    rcases hfirst with hic | hic
    · exact False.elim
        (data.cert.c_ne_i (c2Index data) r hic.symm)
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
    have h20 :
        (Switching.Vertex.lower (.b (c2Index data)) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hp :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact (Switching.Vertex.c0_ne_c2 data.cert).symm hp
    have hfirst :=
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data h20
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
    rw [specialLift_compl_adj_core_b] at hfirst
    rcases hfirst with hic | hic
    · exact False.elim
        (data.cert.c_ne_i (c2Index data) q hic.symm)
    · simpa only [baseProjection_y, baseProjection_b] using
        Gᶜ.adj_symm hic
  ·
    have hqr :=
      (final_blue_adj_y_y_iff data q r).1 hfinal |>.1
    simpa only [baseProjection_y] using i_compl_adj data hqr

/-- No small `B`, `i₂` present, and `b₂` absent: project directly to
`G`. -/
private theorem noX_noSmall_i2_noB2_card_lt
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi2K : Switching.Vertex.core (i2 data) ∈ K)
    (_hb2K : b2 data ∉ K) :
    K.card < s := by
  exact card_lt_of_blue_projection data (baseProjection data) hK
    (fun {_ _} hu hv huv ↦
      baseProjection_maps_adj
        data hKS hK hnoX hb0K hb1K hi2K hu hv huv)
    hG.2

/-- No small `B`, `i₂` and `b₂` both present: replace `b₂` by `c₂`
and project directly to `G`. -/
private theorem noX_noSmall_i2_b2_card_lt
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb0K : b0 data ∉ K) (hb1K : b1 data ∉ K)
    (hi2K : Switching.Vertex.core (i2 data) ∈ K)
    (_hb2K : b2 data ∈ K) :
    K.card < s := by
  exact card_lt_of_blue_projection data (baseProjection data) hK
    (fun {_ _} hu hv huv ↦
      baseProjection_maps_adj
        data hKS hK hnoX hb0K hb1K hi2K hu hv huv)
    hG.2

/-- When exactly one small `B` vertex `b_r` occurs and `b₂` does not,
replace `b_r` by `a_r`; all other relevant vertices use the basic
projection. -/
private def smallBProjection
    (data : Certificates.PlusCaseBData G k s)
    (r : Fin (k - 1)) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core d)) => .core d
  | .inl (.core (.a p)) => .a p
  | .inl (.core (.b _)) => .a r
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some t => .core (data.cert.i t)
      | none => .core (i2 data)
  | _ => .core (i2 data)

@[simp]
private theorem smallBProjection_core
    (data : Certificates.PlusCaseBData G k s)
    (r : Fin (k - 1)) (d : V) :
    smallBProjection data r (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem smallBProjection_b
    (data : Certificates.PlusCaseBData G k s)
    (r p : Fin (k - 1)) :
    smallBProjection data r (Switching.Vertex.b p) = .a r :=
  rfl

@[simp]
private theorem smallBProjection_y
    (data : Certificates.PlusCaseBData G k s)
    (r : Fin (k - 1)) (q : Fin (s - 1)) :
    smallBProjection data r
        (Switching.Vertex.y data.cert (some q)) =
      .core (data.cert.i q) := by
  simp [smallBProjection, Switching.Vertex.y]

/-- Restricted classifier for the fourth no-`X` subcase. -/
private theorem smallB_noB2_member_cases
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (r : Fin (k - 1)) (hrSmall : r.val < 2)
    (hbrK : Switching.Vertex.b r ∈ K)
    (hb2K : b2 data ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      (∀ p, d ≠ data.cert.c p) ∧ ¬G.Adj (i2 data) d) ∨
    v = Switching.Vertex.b r ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q) ∧
        q ≠ i2Index data) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · exact Or.inl hcore
  · subst v
    have hblue := hK hbrK hv (by simp [a2])
    have hfinal :=
      blue_adj_implies_final_blue data (hKS hbrK) (hKS hv) hblue
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_b_a] at hfirst
    have hval := congrArg Fin.val hfirst
    simp [c2Index, Certificates.c2Index] at hval
    omega
  · obtain ⟨p, rfl, hp3⟩ := hb
    by_cases hpr : p = r
    · subst p
      exact Or.inr (Or.inl rfl)
    ·
      have hpSmall : p.val < 2 := by
        by_contra hpNot
        have hp2 : p = c2Index data := by
          apply Fin.ext
          simp [c2Index, Certificates.c2Index]
          omega
        subst p
        exact hb2K hv
      have hblue := hK hbrK hv (by simpa using (Ne.symm hpr))
      have hfinal :=
        blue_adj_implies_final_blue data (hKS hbrK) (hKS hv) hblue
      have hfirst := final_blue_lower_lower_to_first data hfinal
      have hnotPart :=
        (specialLift_compl_adj_b_b G data.cert.c r p).1 hfirst |>.2
      exact False.elim (hnotPart (Or.inl ⟨hrSmall, hpSmall⟩))
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · exact Or.inr (Or.inr hy)

/-- The fourth no-`X` projection preserves blue adjacency. -/
private theorem smallBProjection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (r : Fin (k - 1)) (hrSmall : r.val < 2)
    (hbrK : Switching.Vertex.b r ∈ K)
    (hb2K : b2 data ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (smallBProjection data r u) (smallBProjection data r v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases smallB_noB2_member_cases
      data hKS hK hnoX r hrSmall hbrK hb2K hu with
      ⟨d, rfl, hdC, _⟩ | rfl | ⟨q, rfl, hq2⟩ <;>
    rcases smallB_noB2_member_cases
      data hKS hK hnoX r hrSmall hbrK hb2K hv with
      ⟨e, rfl, heC, _⟩ | rfl | ⟨t, rfl, ht2⟩
  · simpa only [smallBProjection_core] using
      final_blue_lower_lower_to_first data hfinal
  ·
    rw [smallBProjection_core, smallBProjection_b,
      specialLift_compl_adj_core_a]
    exact (hdC r).symm
  ·
    have hd0 :
        (Switching.Vertex.lower (.core d) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    simpa only [smallBProjection_core, smallBProjection_y] using
      final_blue_lower_y_to_first data hd0 hfinal
  ·
    rw [smallBProjection_b, smallBProjection_core,
      specialLift_compl_adj_a_core]
    exact (heC r).symm
  · exact False.elim ((BlueGraph data).loopless.irrefl _ huv)
  ·
    rw [smallBProjection_b, smallBProjection_y,
      specialLift_compl_adj_a_core]
    exact data.cert.c_ne_i r t
  ·
    have he0 :
        (Switching.Vertex.lower (.core e) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    simpa only [smallBProjection_y, smallBProjection_core] using
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
  ·
    rw [smallBProjection_y, smallBProjection_b,
      specialLift_compl_adj_core_a]
    exact data.cert.c_ne_i r q
  ·
    have hqt :=
      (final_blue_adj_y_y_iff data q t).1 hfinal |>.1
    simpa only [smallBProjection_y,
      specialLift_compl_adj_core_core] using i_compl_adj data hqt

/-- Exactly one small `B` vertex and no `b₂`: replace it by its matching
`A` vertex and adjoin `i₂` in the first lift. -/
private theorem noX_smallB_noB2_card_lt
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (r : Fin (k - 1)) (hrSmall : r.val < 2)
    (hbrK : Switching.Vertex.b r ∈ K)
    (hb2K : b2 data ∉ K) :
    K.card < s := by
  classical
  have hr2 : r ≠ c2Index data := by
    intro hr
    have hval := congrArg Fin.val hr
    simp [c2Index, Certificates.c2Index] at hval
    omega
  have hadj :
      ∀ {u v}, u ∈ K → v ∈ K →
        (BlueGraph data).Adj u v →
        (specialLift G data.cert.c)ᶜ.Adj
          (smallBProjection data r u) (smallBProjection data r v) :=
    fun {_ _} hu hv huv ↦
      smallBProjection_maps_adj
        data hKS hK hnoX r hrSmall hbrK hb2K hu hv huv
  have hadjoin :
      ∀ {u}, u ∈ K →
        (specialLift G data.cert.c)ᶜ.Adj
          (smallBProjection data r u) (.core (i2 data)) := by
    intro u hu
    rcases smallB_noB2_member_cases
        data hKS hK hnoX r hrSmall hbrK hb2K hu with
        ⟨d, rfl, hdC, hdblue⟩ | rfl | ⟨q, rfl, hq2⟩
    ·
      have hdi : d ≠ i2 data := by
        intro hdi
        subst d
        have hblue := hK hbrK hu (by simp)
        have hfinal :=
          blue_adj_implies_final_blue data (hKS hbrK) (hKS hu) hblue
        have hfirst := final_blue_lower_lower_to_first data hfinal
        rw [specialLift_compl_adj_b_core] at hfirst
        rcases hfirst with hic | hic
        · exact data.cert.c_ne_i r (i2Index data) hic.symm
        · exact ((SimpleGraph.compl_adj _ _ _).1 hic).2
            (c_adj_i2_of_ne_c2 data r hr2)
      rw [smallBProjection_core, specialLift_compl_adj_core_core,
        SimpleGraph.compl_adj]
      exact ⟨hdi, by simpa [G.adj_comm] using hdblue⟩
    ·
      rw [smallBProjection_b, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i r (i2Index data)
    ·
      rw [smallBProjection_y, specialLift_compl_adj_core_core]
      exact i_compl_adj data hq2
  have hfirst :
      IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  have hlt :
      K.card + 1 < s + 1 :=
    card_succ_lt_of_blue_projection data
      (smallBProjection data r) (.core (i2 data))
      hK hadj hadjoin hfirst.2
  omega

private abbrev c1BIndex
    (data : Certificates.PlusCaseBData G k s) : Fin (k - 1) :=
  Certificates.c1Index data.cert.five_le_k

private theorem c1B_ne_c2
    (data : Certificates.PlusCaseBData G k s) :
    c1BIndex data ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c1BIndex, c2Index, Certificates.c1Index,
    Certificates.c2Index] at hval

/-- In the final no-`X` subcase, replace `b₁` by `a₂`, retain `b₂`,
and use the basic projection on core and `Y` vertices. -/
private def b1b2Projection
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core d)) => .core d
  | .inl (.core (.a p)) => .a p
  | .inl (.core (.b p)) =>
      if p = c2Index data then .b p else .a (c2Index data)
  | .inl (.b q) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) q with
      | some t => .core (data.cert.i t)
      | none => .core (i2 data)
  | _ => .core (i2 data)

@[simp]
private theorem b1b2Projection_core
    (data : Certificates.PlusCaseBData G k s) (d : V) :
    b1b2Projection data (Switching.Vertex.core d) = .core d :=
  rfl

@[simp]
private theorem b1b2Projection_b1
    (data : Certificates.PlusCaseBData G k s) :
    b1b2Projection data (b1 data) = .a (c2Index data) := by
  simp [b1b2Projection, b1, c1BIndex, c1B_ne_c2 data]

@[simp]
private theorem b1b2Projection_b2
    (data : Certificates.PlusCaseBData G k s) :
    b1b2Projection data (b2 data) = .b (c2Index data) := by
  simp [b1b2Projection, b2]

@[simp]
private theorem b1b2Projection_y
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    b1b2Projection data
        (Switching.Vertex.y data.cert (some q)) =
      .core (data.cert.i q) := by
  simp [b1b2Projection, Switching.Vertex.y]

/-- Restricted classifier for the fifth no-`X` subcase. -/
private theorem b1b2_member_cases
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb1K : b1 data ∈ K) (hb2K : b2 data ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      (∀ p, d ≠ data.cert.c p) ∧ ¬G.Adj (i2 data) d) ∨
    v = b1 data ∨ v = b2 data ∨
    (∃ q : Fin (s - 1),
      v = Switching.Vertex.y data.cert (some q) ∧
        q ≠ i2Index data) := by
  rcases blue_member_cases data (hKS hv) with
      hcore | ha | hb | hx | hy
  · exact Or.inl hcore
  · subst v
    have hblue := hK hb1K hv (by simp [a2, b1])
    have hfinal :=
      blue_adj_implies_final_blue data (hKS hb1K) (hKS hv) hblue
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_b_a] at hfirst
    exact False.elim (c1B_ne_c2 data hfirst.symm)
  · obtain ⟨p, rfl, hp3⟩ := hb
    rcases index_lt_three_cases data p hp3 with hp0 | hp1 | hp2
    ·
      subst p
      have hblue := hK hb1K hv (by
        simpa using
          (Certificates.c0_ne_c1 data.cert.five_le_k).symm)
      have hfinal :=
        blue_adj_implies_final_blue data (hKS hb1K) (hKS hv) hblue
      have hfirst := final_blue_lower_lower_to_first data hfinal
      have hnotPart :=
        (specialLift_compl_adj_b_b G data.cert.c
          (c1BIndex data)
          (Certificates.c0Index data.cert.five_le_k)).1 hfirst |>.2
      exact False.elim (hnotPart (Or.inl ⟨by simp [c1BIndex],
        by simp [Certificates.c0Index]⟩))
    · subst p
      exact Or.inr (Or.inl rfl)
    · subst p
      exact Or.inr (Or.inr (Or.inl rfl))
  · obtain ⟨q, rfl⟩ := hx
    exact False.elim (hnoX q hv)
  · exact Or.inr (Or.inr (Or.inr hy))

/-- The final restricted projection preserves blue adjacency. -/
private theorem b1b2Projection_maps_adj
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb1K : b1 data ∈ K) (hb2K : b2 data ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (BlueGraph data).Adj u v) :
    (specialLift G data.cert.c)ᶜ.Adj
      (b1b2Projection data u) (b1b2Projection data v) := by
  have hfinal :=
    blue_adj_implies_final_blue data (hKS hu) (hKS hv) huv
  rcases b1b2_member_cases
      data hKS hK hnoX hb1K hb2K hu with
      ⟨d, rfl, hdC, _⟩ | rfl | rfl | ⟨q, rfl, hq2⟩ <;>
    rcases b1b2_member_cases
      data hKS hK hnoX hb1K hb2K hv with
      ⟨e, rfl, heC, _⟩ | rfl | rfl | ⟨t, rfl, ht2⟩
  · simpa only [b1b2Projection_core] using
      final_blue_lower_lower_to_first data hfinal
  ·
    rw [b1b2Projection_core, b1b2Projection_b1,
      specialLift_compl_adj_core_a]
    exact (hdC (c2Index data)).symm
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_core_b] at hfirst
    rcases hfirst with hdc | hdc
    · exact False.elim (hdC (c2Index data) hdc)
    ·
      rw [b1b2Projection_core, b1b2Projection_b2,
        specialLift_compl_adj_core_b]
      exact Or.inr hdc
  ·
    have hd0 :
        (Switching.Vertex.lower (.core d) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    simpa only [b1b2Projection_core, b1b2Projection_y] using
      final_blue_lower_y_to_first data hd0 hfinal
  ·
    rw [b1b2Projection_b1, b1b2Projection_core,
      specialLift_compl_adj_a_core]
    exact (heC (c2Index data)).symm
  · exact False.elim ((BlueGraph data).loopless.irrefl _ huv)
  ·
    rw [b1b2Projection_b1, b1b2Projection_b2,
      specialLift_compl_adj_a_b]
  ·
    rw [b1b2Projection_b1, b1b2Projection_y,
      specialLift_compl_adj_a_core]
    exact data.cert.c_ne_i (c2Index data) t
  ·
    have hfirst := final_blue_lower_lower_to_first data hfinal
    rw [specialLift_compl_adj_b_core] at hfirst
    rcases hfirst with hec | hec
    · exact False.elim (heC (c2Index data) hec)
    ·
      rw [b1b2Projection_b2, b1b2Projection_core,
        specialLift_compl_adj_b_core]
      exact Or.inr hec
  ·
    rw [b1b2Projection_b2, b1b2Projection_b1,
      specialLift_compl_adj_b_a]
  · exact False.elim ((BlueGraph data).loopless.irrefl _ huv)
  ·
    have h20 :
        (Switching.Vertex.lower (.b (c2Index data)) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hp :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact (Switching.Vertex.c0_ne_c2 data.cert).symm hp
    simpa only [b1b2Projection_b2, b1b2Projection_y] using
      final_blue_lower_y_to_first data h20 hfinal
  ·
    have he0 :
        (Switching.Vertex.lower (.core e) :
          Switching.Vertex V k s) ≠ b0 data := by simp [b0]
    simpa only [b1b2Projection_y, b1b2Projection_core] using
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data he0
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
  ·
    rw [b1b2Projection_y, b1b2Projection_b1,
      specialLift_compl_adj_core_a]
    exact data.cert.c_ne_i (c2Index data) q
  ·
    have h20 :
        (Switching.Vertex.lower (.b (c2Index data)) :
          Switching.Vertex V k s) ≠ b0 data := by
      intro h
      have hp :=
        SpecialLiftVertex.b.inj
          (SpecialLiftVertex.core.inj (Sum.inl.inj h))
      exact (Switching.Vertex.c0_ne_c2 data.cert).symm hp
    simpa only [b1b2Projection_y, b1b2Projection_b2] using
      (specialLift G data.cert.c)ᶜ.adj_symm
        (final_blue_lower_y_to_first data h20
          ((Switching.finalGraph data.cert)ᶜ.adj_symm hfinal))
  ·
    have hqt :=
      (final_blue_adj_y_y_iff data q t).1 hfinal |>.1
    simpa only [b1b2Projection_y,
      specialLift_compl_adj_core_core] using i_compl_adj data hqt

/-- The switched `b₁,b₂` case: replace `b₁` by `a₂`, retain `b₂`, and
adjoin `i₂` in the first lift. -/
private theorem noX_b1_b2_card_lt
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | ¬redToWB data v})
    (hK : (BlueGraph data).IsClique K)
    (hnoX : ∀ q : Fin (s - 1),
      Switching.Vertex.x data.cert (some q) ∉ K)
    (hb1K : b1 data ∈ K) (hb2K : b2 data ∈ K) :
    K.card < s := by
  classical
  have h12 : c1BIndex data ≠ c2Index data := c1B_ne_c2 data
  have hadj :
      ∀ {u v}, u ∈ K → v ∈ K →
        (BlueGraph data).Adj u v →
        (specialLift G data.cert.c)ᶜ.Adj
          (b1b2Projection data u) (b1b2Projection data v) :=
    fun {_ _} hu hv huv ↦
      b1b2Projection_maps_adj
        data hKS hK hnoX hb1K hb2K hu hv huv
  have hadjoin :
      ∀ {u}, u ∈ K →
        (specialLift G data.cert.c)ᶜ.Adj
          (b1b2Projection data u) (.core (i2 data)) := by
    intro u hu
    rcases b1b2_member_cases
        data hKS hK hnoX hb1K hb2K hu with
        ⟨d, rfl, hdC, hdblue⟩ | rfl | rfl | ⟨q, rfl, hq2⟩
    ·
      have hdi : d ≠ i2 data := by
        intro hdi
        subst d
        have hblue := hK hb1K hu (by simp [b1])
        have hfinal :=
          blue_adj_implies_final_blue data (hKS hb1K) (hKS hu) hblue
        have hfirst := final_blue_lower_lower_to_first data hfinal
        rw [specialLift_compl_adj_b_core] at hfirst
        rcases hfirst with hic | hic
        · exact data.cert.c_ne_i
            (c1BIndex data) (i2Index data) hic.symm
        · exact ((SimpleGraph.compl_adj _ _ _).1 hic).2
            (c_adj_i2_of_ne_c2 data (c1BIndex data) h12)
      rw [b1b2Projection_core, specialLift_compl_adj_core_core,
        SimpleGraph.compl_adj]
      exact ⟨hdi, by simpa [G.adj_comm] using hdblue⟩
    ·
      rw [b1b2Projection_b1, specialLift_compl_adj_a_core]
      exact data.cert.c_ne_i (c2Index data) (i2Index data)
    ·
      rw [b1b2Projection_b2, specialLift_compl_adj_b_core]
      exact Or.inr (c2_compl_adj_i2 data)
    ·
      rw [b1b2Projection_y, specialLift_compl_adj_core_core]
      exact i_compl_adj data hq2
  have hfirst :
      IsRamseyFree (specialLift G data.cert.c) k (s + 1) :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  have hlt :
      K.card + 1 < s + 1 :=
    card_succ_lt_of_blue_projection data
      (b1b2Projection data) (.core (i2 data))
      hK hadj hadjoin hfirst.2
  omega

/-- The first-stage switch makes `b₀b₂` red, so the two vertices cannot
coexist in a blue clique in the edited old graph. -/
private theorem not_blue_b0_b2
    (data : Certificates.PlusCaseBData G k s) :
    ¬(BlueGraph data).Adj (b0 data) (b2 data) := by
  intro hblue
  have hb0Blue : ¬redToWB data (b0 data) := by
    rw [redToWB_b]
    simp [b0, Certificates.c0Index]
  have hb2Blue : ¬redToWB data (b2 data) := by
    rw [redToWB_b]
    simp [b2, c2Index, Certificates.c2Index]
  have hfinal :=
    blue_adj_implies_final_blue data hb0Blue hb2Blue hblue
  have hadd :
      (Switching.addedRedGraph data.cert).Adj
        (b0 data) (b2 data) := by
    rw [Switching.addedRedGraph_adj_iff]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hred :
      (Switching.finalGraph data.cert).Adj
        (b0 data) (b2 data) :=
    (Switching.final_adj_iff data.cert _ _).2 (Or.inr hadd)
  exact ((SimpleGraph.compl_adj _ _ _).1 hfinal).2 hred

/-! ## Public assembly -/

/-- The blue neighborhood of the second Type B connector
contains no clique of order `s`. -/
theorem blueNeighborhoodB_cliqueFree
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    (extraBOldGraph data)ᶜ.CliqueFreeOn
      {v | ¬redToWB data v} s := by
  classical
  intro K hKS hK
  have hlt : K.card < s := by
    by_cases hhasX :
        ∃ q : Fin (s - 1),
          Switching.Vertex.x data.cert (some q) ∈ K
    · obtain ⟨q, hqx⟩ := hhasX
      by_cases hsecond :
          ∃ r : Fin (s - 1),
            Switching.Vertex.x data.cert (some r) ∈ K ∧ r ≠ q
      · obtain ⟨r, hrx, hrq⟩ := hsecond
        exact blue_clique_card_lt_of_two_x
          data hKS hK.isClique hqx hrx (Ne.symm hrq)
      ·
        have honly :
            ∀ r : Fin (s - 1),
              Switching.Vertex.x data.cert (some r) ∈ K → r = q := by
          intro r hrx
          by_contra hrq
          exact hsecond ⟨r, hrx, hrq⟩
        exact blue_clique_card_lt_of_one_x
          data hKS hK.isClique q hqx honly
    ·
      have hnoX :
          ∀ q : Fin (s - 1),
            Switching.Vertex.x data.cert (some q) ∉ K :=
        fun q hqx ↦ hhasX ⟨q, hqx⟩
      by_cases hb0K : b0 data ∈ K
      · by_cases hb2K : b2 data ∈ K
        ·
          exact False.elim
            (not_blue_b0_b2 data
              (hK.isClique hb0K hb2K (by
                simpa using Switching.Vertex.c0_ne_c2 data.cert)))
        ·
          exact noX_smallB_noB2_card_lt
            data hG hKS hK.isClique hnoX
            (Certificates.c0Index data.cert.five_le_k)
            (by simp [Certificates.c0Index])
            hb0K hb2K
      · by_cases hb1K : b1 data ∈ K
        · by_cases hb2K : b2 data ∈ K
          · exact noX_b1_b2_card_lt
              data hG hKS hK.isClique hnoX hb1K hb2K
          · exact noX_smallB_noB2_card_lt
              data hG hKS hK.isClique hnoX
              (c1BIndex data)
              (by simp [c1BIndex, Certificates.c1Index])
              hb1K hb2K
        ·
          by_cases hi2K : Switching.Vertex.core (i2 data) ∈ K
          · by_cases hb2K : b2 data ∈ K
            · exact noX_noSmall_i2_b2_card_lt
                data hG hKS hK.isClique hnoX
                hb0K hb1K hi2K hb2K
            · exact noX_noSmall_i2_noB2_card_lt
                data hG hKS hK.isClique hnoX
                hb0K hb1K hi2K hb2K
          · exact noX_noSmall_noI2_card_lt
              data hG hKS hK.isClique hnoX
              hb0K hb1K hi2K
  have hcard := hK.card_eq
  omega

end TypeB
end SecondConnector
end RamseyIncrement
