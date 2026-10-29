/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Construction
import Mathlib.Tactic

/-!
# Safety of the blue switching edges

This file formalizes rows (B1)--(B6) of the switching table in
`PROOF.md`.  A blue dangerous edge is safe when its common blue
neighborhood in the final graph contains no blue clique of order `s - 1`.
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

private noncomputable abbrev BlueGraph
    (cert : Certificates.OrderedCertificates G k s) :=
  (finalGraph cert)ᶜ

private theorem final_compl_adj_iff
    (cert : Certificates.OrderedCertificates G k s)
    (u v : Vertex V k s) :
    (BlueGraph cert).Adj u v ↔
      u ≠ v ∧
        (¬(preGraph cert).Adj u v ∨
          (removedRedGraph cert).Adj u v) ∧
        ¬(addedRedGraph cert).Adj u v := by
  simp only [BlueGraph, SimpleGraph.compl_adj, final_adj_iff]
  tauto

private theorem blue_adj_x_x_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
  (BlueGraph cert).Adj (Vertex.x cert r) (Vertex.x cert t) ↔ r ≠ t := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.x]

@[simp]
private theorem secondCertificate_some
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    Canonical.secondCertificate cert.toCertificates cert.five_le_k
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s))
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm (some q)) =
      .core (cert.i q) := by
  rw [Canonical.secondCertificate_apply]
  simp [Canonical.secondCertificateAt]

@[simp]
private theorem secondCertificate_none
    (cert : Certificates.OrderedCertificates G k s) :
    Canonical.secondCertificate cert.toCertificates cert.five_le_k
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s))
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm none) =
      .a (Vertex.c0 cert) := by
  rw [Canonical.secondCertificate_apply]
  simp [Canonical.secondCertificateAt, Vertex.c0]

private theorem pre_blue_adj_x_lower_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) (v : SpecialLiftVertex V k) :
    (preGraph cert)ᶜ.Adj (Vertex.x cert r) (.inl (.core v)) ↔
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r = v := by
  simp [preGraph, canonicalGraph, Canonical.graph, Vertex.x,
    Canonical.secondCertificate_apply, redJoinedClone]
  change
    Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s)))
          ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              (cert.five_le_s))).symm r)) = v ↔
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r = v
  simp

private theorem blue_adj_xSome_core_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (v : V) :
    (BlueGraph cert).Adj (Vertex.x cert (some q)) (Vertex.core v) ↔
      v = cert.i q := by
  have hpre := pre_blue_adj_x_lower_iff cert (some q)
    (SpecialLiftVertex.core v)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.core, eq_comm]

private theorem blue_adj_xSome_a_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (BlueGraph cert).Adj (Vertex.x cert (some q)) (Vertex.a p) ↔
      q ∈ cert.E ∧ p = Vertex.c0 cert := by
  have hpre := pre_blue_adj_x_lower_iff cert (some q)
    (SpecialLiftVertex.a p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.a, Vertex.c0,
    and_comm, and_left_comm, and_assoc]

private theorem blue_adj_xSome_b_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (BlueGraph cert).Adj (Vertex.x cert (some q)) (Vertex.b p) ↔
      q = Vertex.i1 cert ∧ p = Vertex.c0 cert := by
  have hpre := pre_blue_adj_x_lower_iff cert (some q)
    (SpecialLiftVertex.b p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.b, Vertex.c0,
    Vertex.i1, and_comm, and_left_comm, and_assoc]

private theorem common_b0_x1_cases
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {w : Vertex V k s}
    (hb : (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w)
    (hx : (BlueGraph cert).Adj
      (Vertex.x cert (some (Vertex.i1 cert))) w) :
    w = Vertex.core (cert.i (Vertex.i1 cert)) ∨
      w = Vertex.x cert none ∨
      (∃ q : Fin (s - 1),
        w = Vertex.y cert (some q) ∧ q ≠ Vertex.i1 cert) ∨
      (cert.E.Nonempty ∧
        w = Vertex.a (Vertex.c0 cert)) := by
  rcases w with w | u
  · rcases w with w | r | r
    · rcases w with v | p | p
      · left
        simpa [Vertex.core] using
          (blue_adj_xSome_core_iff cert (Vertex.i1 cert) v).1 hx
      · have hp : p = Vertex.c0 cert := by
          simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
            removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
            Vertex.x, Vertex.c0, Vertex.i1,
            redJoinedClone] using hb
        subst p
        right; right; right
        refine ⟨?_, rfl⟩
        rw [cert.E_nonempty_iff_i1_mem hG]
        exact (blue_adj_xSome_a_iff cert (Vertex.i1 cert)
          (Vertex.c0 cert)).1 hx |>.1
      · have hp : p = Vertex.c0 cert := by
          exact (blue_adj_xSome_b_iff cert (Vertex.i1 cert) p).1 hx |>.2
        subst p
        exact False.elim ((BlueGraph cert).loopless.irrefl _ hb)
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hx ⊢
      cases o with
      | none => exact Or.inr (Or.inl rfl)
      | some q =>
          have hq : q = Vertex.i1 cert :=
            (blue_adj_xSome_b_iff cert q (Vertex.c0 cert)).1
              ((BlueGraph cert).adj_symm hb) |>.1
          have hne : (some (Vertex.i1 cert) : Option (Fin (s - 1))) ≠ some q :=
            (blue_adj_x_x_iff cert _ _).1 hx
          exact False.elim (hne (congrArg some hq.symm))
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hx ⊢
      cases o with
      | none =>
          simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
            removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
            Vertex.y, Vertex.c0, redJoinedClone] at hb
      | some q =>
          right; right; left
          refine ⟨q, rfl, ?_⟩
          have hx' : Vertex.i1 cert ≠ q := by
            simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
            removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
            Vertex.x, Vertex.y, Vertex.c0, Vertex.i1,
            redJoinedClone] using hx
          exact hx'.symm
  ·
    exact False.elim (by
      simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
        removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
        Vertex.c0, redJoinedClone] using hb)

private theorem blue_adj_ySome_ySome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q r : Fin (s - 1)) :
    (BlueGraph cert).Adj
        (Vertex.y cert (some q)) (Vertex.y cert (some r)) ↔
      q ≠ r ∧
        (SameBPart (k := s + 1)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                (cert.five_le_s))).symm (some q))
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                (cert.five_le_s))).symm (some r)) ∨
          (q = Vertex.i1 cert ∧ r ∈ cert.E ∧ 2 ≤ r.val) ∨
          (r = Vertex.i1 cert ∧ q ∈ cert.E ∧ 2 ≤ q.val)) := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.y, Vertex.i1, redJoinedClone]
  tauto

private theorem blue_adj_ySome_same_part_of_ne_i1
    (cert : Certificates.OrderedCertificates G k s)
    {q r : Fin (s - 1)}
    (hq : q ≠ Vertex.i1 cert) (hr : r ≠ Vertex.i1 cert)
    (hqr : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some r))) :
    (q.val < 2 ∧ r.val < 2) ∨
      (2 ≤ q.val ∧ 2 ≤ r.val) := by
  rcases (blue_adj_ySome_ySome_iff cert q r).1 hqr with
    ⟨_, hpart | hswitch | hswitch⟩
  · simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
  · exact False.elim (hq hswitch.1)
  · exact False.elim (hr hswitch.1)
  /-
  have hq1 : q.val ≠ 1 := by
    intro h
    apply hq
    apply Fin.ext
    simpa [Vertex.i1] using h
  have hr1 : r.val ≠ 1 := by
    intro h
    apply hr
    apply Fin.ext
    simpa [Vertex.i1] using h
  by_cases hqsmall : q.val < 2
  · left
    refine ⟨hqsmall, ?_⟩
    by_contra hrsmall
    have hrlarge : 2 ≤ r.val := by omega
    have hbad := hlogic (fun _ ↦ by omega)
    omega
  · right
    have hqlarge : 2 ≤ q.val := by omega
    refine ⟨hqlarge, ?_⟩
    have hlarge := hlogic (fun hqle ↦ by omega)
    exact hlarge.2
  -/

private def ySomeEmbedding
    (cert : Certificates.OrderedCertificates G k s) :
    Fin (s - 1) ↪ Vertex V k s where
  toFun q := Vertex.y cert (some q)
  inj' := by
    intro q r h
    have houter :
        (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm (some q) =
        (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm (some r) :=
      SpecialLiftVertex.b.inj (Sum.inl.inj h)
    exact Option.some.inj
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s))).symm.injective houter)

private noncomputable def ySet
    (cert : Certificates.OrderedCertificates G k s)
    (Q : Finset (Fin (s - 1))) : Finset (Vertex V k s) :=
  Q.map (ySomeEmbedding cert)

@[simp]
private theorem mem_ySet
    (cert : Certificates.OrderedCertificates G k s)
    (Q : Finset (Fin (s - 1))) (q : Fin (s - 1)) :
    Vertex.y cert (some q) ∈ ySet cert Q ↔ q ∈ Q := by
  constructor
  · intro h
    obtain ⟨r, hr, heq⟩ := Finset.mem_map.1 h
    have hrq : r = q := (ySomeEmbedding cert).injective heq
    simpa [hrq] using hr
  · intro h
    exact Finset.mem_map.2 ⟨q, h, rfl⟩

@[simp]
private theorem card_ySet
    (cert : Certificates.OrderedCertificates G k s)
    (Q : Finset (Fin (s - 1))) :
    (ySet cert Q).card = Q.card := by
  simp [ySet]

private theorem card_le_two_add_ySet
    [DecidableEq V]
    {cert : Certificates.OrderedCertificates G k s}
    {K : Finset (Vertex V k s)} {e₁ e₂ : Vertex V k s}
    {Q : Finset (Fin (s - 1))}
    (hsub : K ⊆ insert e₁ (insert e₂ (ySet cert Q))) :
    K.card ≤ 2 + Q.card := by
  have h₀ := Finset.card_le_card hsub
  have h₁ :
      (insert e₁ (insert e₂ (ySet cert Q))).card ≤
        (insert e₂ (ySet cert Q)).card + 1 :=
    Finset.card_insert_le _ _
  have h₂ :
      (insert e₂ (ySet cert Q)).card ≤ (ySet cert Q).card + 1 :=
    Finset.card_insert_le _ _
  rw [card_ySet] at h₂
  omega

private theorem card_le_one_add_ySet
    [DecidableEq V]
    {cert : Certificates.OrderedCertificates G k s}
    {K : Finset (Vertex V k s)} {e : Vertex V k s}
    {Q : Finset (Fin (s - 1))}
    (hsub : K ⊆ insert e (ySet cert Q)) :
    K.card ≤ 1 + Q.card := by
  have h₀ := Finset.card_le_card hsub
  have h₁ :
      (insert e (ySet cert Q)).card ≤ (ySet cert Q).card + 1 :=
    Finset.card_insert_le _ _
  rw [card_ySet] at h₁
  omega

private theorem blue_adj_x_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (BlueGraph cert).Adj (Vertex.x cert r) (Vertex.y cert t) ↔
      r ≠ t := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.x, Vertex.y, redJoinedClone]

private theorem not_blue_adj_xNone_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    ¬(BlueGraph cert).Adj (Vertex.x cert none) (Vertex.core v) := by
  have hpre := pre_blue_adj_x_lower_iff cert none
    (SpecialLiftVertex.core v)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.core]

private theorem pre_blue_adj_lower_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (v : SpecialLiftVertex V k) (r : Option (Fin (s - 1))) :
    (preGraph cert)ᶜ.Adj (.inl (.core v)) (Vertex.y cert r) ↔
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r ≠ v ∧
        (specialLift G cert.c)ᶜ.Adj
          (Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r) v := by
  simp [preGraph, canonicalGraph, Canonical.graph, Vertex.y, redJoinedClone]
  change
    (¬v = Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s)))
          ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              (cert.five_le_s))).symm r)) ∧
      ¬Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
          ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              (cert.five_le_s)))
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                (cert.five_le_s))).symm r)) = v ∧
        ¬(specialLift G cert.c).Adj
          (Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                (cert.five_le_s)))
              ((Canonical.outerIndexEquiv
                (le_trans (by decide : 1 ≤ 5)
                  (cert.five_le_s))).symm r))) v) ↔ _
  simp
  tauto

private theorem blue_adj_a0_ySome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
        q ∈ cert.U := by
  have hpre := pre_blue_adj_lower_y_iff cert
    (SpecialLiftVertex.a (Vertex.c0 cert)) (some q)
  simp [Canonical.secondCertificateAt, Vertex.c0] at hpre
  have hpreNot :
      ¬(preGraph cert).Adj
        (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) :=
    hpre.2 (cert.c_ne_i (Vertex.c0 cert) q)
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, Vertex.a, Vertex.y, Vertex.c0,
    Certificates.OrderedCertificates.mem_U,
    Certificates.OrderedCertificates.mem_T, hpreNot]

/-- Row (B2): the switched edge `b₀x₁` is blue-safe. -/
theorem blue_case_b2
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert))
        (Vertex.x cert (some (Vertex.i1 cert)))) (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w ∧
        (BlueGraph cert).Adj
          (Vertex.x cert (some (Vertex.i1 cert))) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hy_ne_i1 {q : Fin (s - 1)}
      (hqK : Vertex.y cert (some q) ∈ K) :
      q ≠ Vertex.i1 cert := by
    have hne :
        (some (Vertex.i1 cert) : Option (Fin (s - 1))) ≠ some q :=
      (blue_adj_x_y_iff cert _ _).1 (hcommon hqK).2
    intro hq
    exact hne (congrArg some hq.symm)
  have bound_with_a0
      (ha0 : Vertex.a (Vertex.c0 cert) ∈ K)
      (Q : Finset (Fin (s - 1)))
      (hY : ∀ q : Fin (s - 1),
        Vertex.y cert (some q) ∈ K → q ∈ Q) :
      K.card ≤ 2 + Q.card := by
    by_cases hxstar : Vertex.x cert none ∈ K
    · apply card_le_two_add_ySet
        (cert := cert) (e₁ := Vertex.a (Vertex.c0 cert))
        (e₂ := Vertex.x cert none) (Q := Q)
      intro w hw
      rcases common_b0_x1_cases cert hG (hcommon hw).1 (hcommon hw).2 with
        hwcore | hwstar | hwy | hwa0
      · have hadj := hK.isClique hw hxstar (by
          intro heq
          rw [hwcore] at heq
          simp [Vertex.core, Vertex.x] at heq)
        exact False.elim (not_blue_adj_xNone_core cert _ <|
          (BlueGraph cert).adj_symm <| by simpa [hwcore] using hadj)
      · rw [hwstar]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · obtain ⟨q, rfl, -⟩ := hwy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem ((mem_ySet cert Q q).2 (hY q hw)))
      · rw [hwa0.2]
        exact Finset.mem_insert_self _ _
    · apply card_le_two_add_ySet
        (cert := cert) (e₁ := Vertex.a (Vertex.c0 cert))
        (e₂ := Vertex.core (cert.i (Vertex.i1 cert))) (Q := Q)
      intro w hw
      rcases common_b0_x1_cases cert hG (hcommon hw).1 (hcommon hw).2 with
        hwcore | hwstar | hwy | hwa0
      · rw [hwcore]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact False.elim (hxstar (by simpa [hwstar] using hw))
      · obtain ⟨q, rfl, -⟩ := hwy
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem ((mem_ySet cert Q q).2 (hY q hw)))
      · rw [hwa0.2]
        exact Finset.mem_insert_self _ _
  have bound_without_a0
      (ha0 : Vertex.a (Vertex.c0 cert) ∉ K)
      (Q : Finset (Fin (s - 1)))
      (hY : ∀ q : Fin (s - 1),
        Vertex.y cert (some q) ∈ K → q ∈ Q) :
      K.card ≤ 1 + Q.card := by
    by_cases hxstar : Vertex.x cert none ∈ K
    · apply card_le_one_add_ySet
        (cert := cert) (e := Vertex.x cert none) (Q := Q)
      intro w hw
      rcases common_b0_x1_cases cert hG (hcommon hw).1 (hcommon hw).2 with
        hwcore | hwstar | hwy | hwa0
      · have hadj := hK.isClique hw hxstar (by
          intro heq
          rw [hwcore] at heq
          simp [Vertex.core, Vertex.x] at heq)
        exact False.elim (not_blue_adj_xNone_core cert _ <|
          (BlueGraph cert).adj_symm <| by simpa [hwcore] using hadj)
      · rw [hwstar]
        exact Finset.mem_insert_self _ _
      · obtain ⟨q, rfl, -⟩ := hwy
        exact Finset.mem_insert_of_mem ((mem_ySet cert Q q).2 (hY q hw))
      · exact False.elim (ha0 (by simpa [hwa0.2] using hw))
    · apply card_le_one_add_ySet
        (cert := cert) (e := Vertex.core (cert.i (Vertex.i1 cert))) (Q := Q)
      intro w hw
      rcases common_b0_x1_cases cert hG (hcommon hw).1 (hcommon hw).2 with
        hwcore | hwstar | hwy | hwa0
      · rw [hwcore]
        exact Finset.mem_insert_self _ _
      · exact False.elim (hxstar (by simpa [hwstar] using hw))
      · obtain ⟨q, rfl, -⟩ := hwy
        exact Finset.mem_insert_of_mem ((mem_ySet cert Q q).2 (hY q hw))
      · exact False.elim (ha0 (by simpa [hwa0.2] using hw))
  by_cases ha0 : Vertex.a (Vertex.c0 cert) ∈ K
  · have hi1E :
        Vertex.i1 cert ∈ cert.E :=
      (blue_adj_xSome_a_iff cert (Vertex.i1 cert)
        (Vertex.c0 cert)).1 (hcommon ha0).2 |>.1
    have hE : cert.E.Nonempty := ⟨Vertex.i1 cert, hi1E⟩
    obtain ⟨hB⟩ := (cert.E_nonempty_iff_caseB hG).1 hE
    have hULarge : cert.ULarge.card ≤ s - k :=
      le_trans (cert.caseB_card_ULarge_le hB) (Nat.sub_le _ _)
    by_cases hsmall :
        ∃ q : Fin (s - 1),
          Vertex.y cert (some q) ∈ K ∧ q.val < 2
    · obtain ⟨q₀, hq₀K, hq₀small⟩ := hsmall
      have hYsmall (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) :
          r ∈ ({Certificates.i0Index' cert.five_le_s} :
            Finset (Fin (s - 1))) := by
        have hrsmall : r.val < 2 := by
          by_cases hqr : q₀ = r
          · simpa [← hqr] using hq₀small
          · have hadj := hK.isClique hq₀K hrK (by
              intro heq
              exact hqr ((ySomeEmbedding cert).injective heq))
            rcases blue_adj_ySome_same_part_of_ne_i1 cert
                (hy_ne_i1 hq₀K) (hy_ne_i1 hrK) hadj with h | h
            · exact h.2
            · omega
        have hr1 : r.val ≠ 1 := by
          intro hrval
          apply hy_ne_i1 hrK
          apply Fin.ext
          simpa [Vertex.i1] using hrval
        have hr0 :
            r = Certificates.i0Index' cert.five_le_s := by
          apply Fin.ext
          simp
          omega
        simp [hr0]
      have hcard := bound_with_a0 ha0 _ hYsmall
      have hs5 := cert.five_le_s
      have hk := cert.five_le_k
      have hcardK := hK.card_eq
      simp at hcard
      omega
    · have hYlarge (q : Fin (s - 1))
          (hqK : Vertex.y cert (some q) ∈ K) :
          q ∈ cert.ULarge := by
        apply (cert.mem_ULarge q).2
        constructor
        · exact (blue_adj_a0_ySome_iff cert q).1 <|
            hK.isClique ha0 hqK (by simp [Vertex.a, Vertex.y])
        · by_contra hq2
          exact hsmall ⟨q, hqK, by omega⟩
      have hcard := bound_with_a0 ha0 cert.ULarge hYlarge
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs5 := cert.five_le_s
      omega

  · by_cases hsmall :
        ∃ q : Fin (s - 1),
          Vertex.y cert (some q) ∈ K ∧ q.val < 2
    · obtain ⟨q₀, hq₀K, hq₀small⟩ := hsmall
      have hYsmall (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) :
          r ∈ ({Certificates.i0Index' cert.five_le_s} :
            Finset (Fin (s - 1))) := by
        have hrsmall : r.val < 2 := by
          by_cases hqr : q₀ = r
          · simpa [← hqr] using hq₀small
          · have hadj := hK.isClique hq₀K hrK (by
              intro heq
              exact hqr ((ySomeEmbedding cert).injective heq))
            rcases blue_adj_ySome_same_part_of_ne_i1 cert
                (hy_ne_i1 hq₀K) (hy_ne_i1 hrK) hadj with h | h
            · exact h.2
            · omega
        have hr1 : r.val ≠ 1 := by
          intro hrval
          apply hy_ne_i1 hrK
          apply Fin.ext
          simpa [Vertex.i1] using hrval
        have hr0 :
            r = Certificates.i0Index' cert.five_le_s := by
          apply Fin.ext
          simp
          omega
        simp [hr0]
      have hcard := bound_without_a0 ha0 _ hYsmall
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs5 := cert.five_le_s
      simp at hcard
      omega
    · have hYlarge (q : Fin (s - 1))
          (hqK : Vertex.y cert (some q) ∈ K) :
          q ∈ cert.largeIndices := by
        apply (cert.mem_largeIndices_iff q).2
        by_contra hq2
        exact hsmall ⟨q, hqK, by omega⟩
      have hcard := bound_without_a0 ha0 cert.largeIndices hYlarge
      have hcardLarge := cert.card_largeIndices
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs5 := cert.five_le_s
      omega

private theorem blue_adj_xNone_a_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (BlueGraph cert).Adj (Vertex.x cert none) (Vertex.a p) ↔
      p = Vertex.c0 cert := by
  have hpre := pre_blue_adj_x_lower_iff cert none
    (SpecialLiftVertex.a p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.a, Vertex.c0,
    eq_comm]

private theorem blue_adj_xNone_b_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (BlueGraph cert).Adj (Vertex.x cert none) (Vertex.b p) ↔
      p = Vertex.c0 cert := by
  have hpre := pre_blue_adj_x_lower_iff cert none
    (SpecialLiftVertex.b p)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.b, Vertex.c0,
    eq_comm]

private theorem common_b0_xStar_cases
    (cert : Certificates.OrderedCertificates G k s)
    {w : Vertex V k s}
    (hb : (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w)
    (hx : (BlueGraph cert).Adj (Vertex.x cert none) w) :
    w = Vertex.a (Vertex.c0 cert) ∨
      w = Vertex.x cert (some (Vertex.i1 cert)) ∨
      ∃ q : Fin (s - 1), w = Vertex.y cert (some q) := by
  rcases w with w | u
  · rcases w with w | r | r
    · rcases w with v | p | p
      · exact False.elim (not_blue_adj_xNone_core cert v hx)
      · left
        have hp := (blue_adj_xNone_a_iff cert p).1 hx
        simpa [hp]
      · have hp := (blue_adj_xNone_b_iff cert p).1 hx
        subst p
        exact False.elim ((BlueGraph cert).loopless.irrefl _ hb)
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hx ⊢
      cases o with
      | none => exact False.elim ((BlueGraph cert).loopless.irrefl _ hx)
      | some q =>
          right; left
          have hq : q = Vertex.i1 cert :=
            (blue_adj_xSome_b_iff cert q (Vertex.c0 cert)).1
              ((BlueGraph cert).adj_symm hb) |>.1
          simpa [hq]
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hx ⊢
      cases o with
      | none =>
          exact False.elim ((blue_adj_x_y_iff cert none none).1 hx rfl)
      | some q => exact Or.inr (Or.inr ⟨q, rfl⟩)
  · exact False.elim (by
      simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
        removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
        Vertex.c0, redJoinedClone] using hb)

private theorem card_le_ySet
    {cert : Certificates.OrderedCertificates G k s}
    {K : Finset (Vertex V k s)} {Q : Finset (Fin (s - 1))}
    (hsub : K ⊆ ySet cert Q) :
    K.card ≤ Q.card := by
  simpa using Finset.card_le_card hsub

private theorem blue_adj_ySome_same_part_of_mem_U
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q r : Fin (s - 1)}
    (hqU : q ∈ cert.U) (hrU : r ∈ cert.U)
    (hqr : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some r))) :
    (q.val < 2 ∧ r.val < 2) ∨
      (2 ≤ q.val ∧ 2 ≤ r.val) := by
  rcases (blue_adj_ySome_ySome_iff cert q r).1 hqr with
    ⟨_, hpart | hswitch | hswitch⟩
  · simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
  · have hE : cert.E.Nonempty := ⟨r, hswitch.2.1⟩
    have hi1E := (cert.E_nonempty_iff_i1_mem hG).1 hE
    have hi1T := cert.E_subset_T hi1E
    have hqNotT := (cert.mem_U q).1 hqU
    exact False.elim (hqNotT (by simpa [hswitch.1] using hi1T))
  · have hE : cert.E.Nonempty := ⟨q, hswitch.2.1⟩
    have hi1E := (cert.E_nonempty_iff_i1_mem hG).1 hE
    have hi1T := cert.E_subset_T hi1E
    have hrNotT := (cert.mem_U r).1 hrU
    exact False.elim (hrNotT (by simpa [hswitch.1] using hi1T))

/-- Row (B3): the switched edge `b₀x_*` is blue-safe. -/
theorem blue_case_b3
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.x cert none)) (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w ∧
        (BlueGraph cert).Adj (Vertex.x cert none) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hclass {w : Vertex V k s} (hw : w ∈ K) :=
    common_b0_xStar_cases cert (hcommon hw).1 (hcommon hw).2
  by_cases ha0 : Vertex.a (Vertex.c0 cert) ∈ K
  · have hYU (q : Fin (s - 1))
        (hqK : Vertex.y cert (some q) ∈ K) :
        q ∈ cert.U :=
      (blue_adj_a0_ySome_iff cert q).1 <|
        hK.isClique ha0 hqK (by simp [Vertex.a, Vertex.y])
    by_cases hsmall :
        ∃ q : Fin (s - 1),
          Vertex.y cert (some q) ∈ K ∧ q.val < 2
    · obtain ⟨q₀, hq₀K, hq₀small⟩ := hsmall
      have hYsmall (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) : r.val < 2 := by
        by_cases hqr : q₀ = r
        · simpa [← hqr] using hq₀small
        · have hadj := hK.isClique hq₀K hrK (by
            intro heq
            exact hqr ((ySomeEmbedding cert).injective heq))
          rcases blue_adj_ySome_same_part_of_mem_U cert hG
              (hYU q₀ hq₀K) (hYU r hrK) hadj with h | h
          · exact h.2
          · omega
      by_cases hx1 : Vertex.x cert (some (Vertex.i1 cert)) ∈ K
      · have hi1E :=
          (blue_adj_xSome_a_iff cert (Vertex.i1 cert)
            (Vertex.c0 cert)).1
            ((BlueGraph cert).adj_symm <|
              hK.isClique ha0 hx1 (by simp [Vertex.a, Vertex.x])) |>.1
        have hi1T := cert.E_subset_T hi1E
        have hY0 (q : Fin (s - 1))
            (hqK : Vertex.y cert (some q) ∈ K) :
            q ∈ ({Certificates.i0Index' cert.five_le_s} :
              Finset (Fin (s - 1))) := by
          have hqNotT := (cert.mem_U q).1 (hYU q hqK)
          have hq1 : q.val ≠ 1 := by
            intro hqv
            apply hqNotT
            have hqi1 : q = Vertex.i1 cert := by
              apply Fin.ext
              simpa [Vertex.i1] using hqv
            simpa [hqi1] using hi1T
          have hq0 :
              q = Certificates.i0Index' cert.five_le_s := by
            apply Fin.ext
            simp
            have := hYsmall q hqK
            omega
          simp [hq0]
        have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert))
              (insert (Vertex.x cert (some (Vertex.i1 cert)))
                (ySet cert
                  {Certificates.i0Index' cert.five_le_s})) := by
          intro w hw
          rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
          · simpa [hwa]
          · simpa [hwx]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem ((mem_ySet cert _ q).2 (hY0 q hw)))
        have hcard := card_le_two_add_ySet
          (cert := cert) (e₁ := Vertex.a (Vertex.c0 cert))
          (e₂ := Vertex.x cert (some (Vertex.i1 cert)))
          (Q := {Certificates.i0Index' cert.five_le_s}) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        simp at hcard
        omega
      · let Qsmall : Finset (Fin (s - 1)) :=
          {Certificates.i0Index' cert.five_le_s,
            Vertex.i1 cert}
        have hYQ (q : Fin (s - 1))
            (hqK : Vertex.y cert (some q) ∈ K) : q ∈ Qsmall := by
          have hq := hYsmall q hqK
          have hqi :
              q = Certificates.i0Index' cert.five_le_s ∨
                q = Vertex.i1 cert := by
            by_cases hq0 : q.val = 0
            · left
              apply Fin.ext
              simpa using hq0
            · right
              apply Fin.ext
              simp [Vertex.i1]
              omega
          simpa [Qsmall] using hqi
        have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert)) (ySet cert Qsmall) := by
          intro w hw
          rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
          · simpa [hwa]
          · exact False.elim (hx1 (by simpa [hwx] using hw))
          · exact Finset.mem_insert_of_mem ((mem_ySet cert Qsmall q).2 (hYQ q hw))
        have hcard := card_le_one_add_ySet
          (cert := cert) (e := Vertex.a (Vertex.c0 cert))
          (Q := Qsmall) hsub
        have hQ : Qsmall.card ≤ 2 := by
          simpa [Qsmall] using
            (Finset.card_insert_le
              (Certificates.i0Index' cert.five_le_s)
              ({Vertex.i1 cert} : Finset (Fin (s - 1))))
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega

    · have hYlarge (q : Fin (s - 1))
          (hqK : Vertex.y cert (some q) ∈ K) :
          q ∈ cert.ULarge :=
        (cert.mem_ULarge q).2 ⟨hYU q hqK, by
          by_contra hq
          exact hsmall ⟨q, hqK, by omega⟩⟩
      by_cases hx1 : Vertex.x cert (some (Vertex.i1 cert)) ∈ K
      · have hi1E :=
          (blue_adj_xSome_a_iff cert (Vertex.i1 cert)
            (Vertex.c0 cert)).1
            ((BlueGraph cert).adj_symm <|
              hK.isClique ha0 hx1 (by simp [Vertex.a, Vertex.x])) |>.1
        obtain ⟨hB⟩ := (cert.E_nonempty_iff_caseB hG).1 ⟨_, hi1E⟩
        have hUL := cert.caseB_card_ULarge_le hB
        have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert))
              (insert (Vertex.x cert (some (Vertex.i1 cert)))
                (ySet cert cert.ULarge)) := by
          intro w hw
          rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
          · simpa [hwa]
          · simpa [hwx]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem ((mem_ySet cert _ q).2 (hYlarge q hw)))
        have hcard := card_le_two_add_ySet
          (cert := cert) (e₁ := Vertex.a (Vertex.c0 cert))
          (e₂ := Vertex.x cert (some (Vertex.i1 cert)))
          (Q := cert.ULarge) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega
      · have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert))
              (ySet cert cert.ULarge) := by
          intro w hw
          rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
          · simpa [hwa]
          · exact False.elim (hx1 (by simpa [hwx] using hw))
          · exact Finset.mem_insert_of_mem ((mem_ySet cert _ q).2 (hYlarge q hw))
        have hcard := card_le_one_add_ySet
          (cert := cert) (e := Vertex.a (Vertex.c0 cert))
          (Q := cert.ULarge) hsub
        have hUL : cert.ULarge.card ≤ s - 3 := by
          rw [← cert.card_largeIndices]
          exact Finset.card_le_card Finset.inter_subset_right
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega
  · by_cases hcross :
        Vertex.y cert (some (Vertex.i1 cert)) ∈ K ∧
          ∃ r : Fin (s - 1),
            Vertex.y cert (some r) ∈ K ∧ 2 ≤ r.val
    · obtain ⟨hy1K, r₀, hr₀K, hr₀large⟩ := hcross
      let Qcross : Finset (Fin (s - 1)) :=
        insert (Vertex.i1 cert) cert.ELarge
      have hYcross (q : Fin (s - 1))
          (hqK : Vertex.y cert (some q) ∈ K) : q ∈ Qcross := by
        by_cases hqi1 : q = Vertex.i1 cert
        · simp [Qcross, hqi1]
        · have hadj1 := hK.isClique hy1K hqK (by
            intro heq
            exact hqi1 ((ySomeEmbedding cert).injective heq.symm))
          rcases (blue_adj_ySome_ySome_iff cert (Vertex.i1 cert) q).1 hadj1 with
            ⟨_, hpart | hswitch | hswitch⟩
          · have hs : (Vertex.i1 cert).val < 2 ∧ q.val < 2 ∨
                2 ≤ (Vertex.i1 cert).val ∧ 2 ≤ q.val := by
              simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
            have hqsmall : q.val < 2 := by
              rcases hs with hs | hs
              · exact hs.2
              · simp [Vertex.i1] at hs
            have hadj := hK.isClique hqK hr₀K (by
              intro heq
              have heq' := (ySomeEmbedding cert).injective heq
              subst q
              omega)
            rcases (blue_adj_ySome_ySome_iff cert q r₀).1 hadj with
              ⟨_, hpart' | hswitch' | hswitch'⟩
            · have hs' : q.val < 2 ∧ r₀.val < 2 ∨
                  2 ≤ q.val ∧ 2 ≤ r₀.val := by
                simpa [Canonical.outerIndexEquiv, SameBPart] using hpart'
              rcases hs' with hs' | hs' <;> omega
            · exact False.elim (hqi1 hswitch'.1)
            · have hr₀one := congrArg Fin.val hswitch'.1
              simp [Vertex.i1] at hr₀one
              omega
          · apply Finset.mem_insert_of_mem
            exact (cert.mem_ELarge q).2 ⟨hswitch.2.1, hswitch.2.2⟩
          · exact False.elim (hqi1 hswitch.1)
      have hsub : K ⊆ ySet cert Qcross := by
        intro w hw
        rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
        · exact False.elim (ha0 (by simpa [hwa] using hw))
        · have hadj := hK.isClique hw hy1K (by
            intro heq
            rw [hwx] at heq
            simp [Vertex.x, Vertex.y] at heq)
          have hadj' : (BlueGraph cert).Adj
              (Vertex.x cert (some (Vertex.i1 cert)))
              (Vertex.y cert (some (Vertex.i1 cert))) := by
            simpa [hwx] using hadj
          exact False.elim ((blue_adj_x_y_iff cert _ _).1 hadj' rfl)
        · exact (mem_ySet cert Qcross q).2 (hYcross q hw)
      have hcard := card_le_ySet hsub
      have hQ : Qcross.card ≤ cert.ELarge.card + 1 := by
        exact Finset.card_insert_le _ _
      have hr₀ne : r₀ ≠ Vertex.i1 cert := by
        intro h
        have := congrArg Fin.val h
        simp [Vertex.i1] at this
        omega
      have hr₀EL : r₀ ∈ cert.ELarge := by
        have hr₀Q := hYcross r₀ hr₀K
        simpa [Qcross, hr₀ne] using hr₀Q
      obtain ⟨hB⟩ := (cert.E_nonempty_iff_caseB hG).1
        ⟨r₀, ((cert.mem_ELarge r₀).1 hr₀EL).1⟩
      have hEL := cert.caseB_card_ELarge_le hB
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs5 := cert.five_le_s
      omega
    · by_cases hsmall :
          ∃ q : Fin (s - 1),
            Vertex.y cert (some q) ∈ K ∧ q.val < 2
      · obtain ⟨q₀, hq₀K, hq₀small⟩ := hsmall
        have hYsmall (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) : r.val < 2 := by
          by_cases hqr : q₀ = r
          · simpa [← hqr] using hq₀small
          · by_cases hq1 : q₀ = Vertex.i1 cert
            · by_contra hr2
              exact hcross ⟨by simpa [← hq1] using hq₀K,
                r, hrK, by omega⟩
            · have hadj := hK.isClique hq₀K hrK (by
                intro heq
                exact hqr ((ySomeEmbedding cert).injective heq))
              rcases (blue_adj_ySome_ySome_iff cert q₀ r).1 hadj with
                ⟨_, hpart | hswitch | hswitch⟩
              · have hs : q₀.val < 2 ∧ r.val < 2 ∨
                    2 ≤ q₀.val ∧ 2 ≤ r.val := by
                  simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
                rcases hs with hs | hs <;> omega
              · exact False.elim (hq1 hswitch.1)
              · omega
        by_cases hx1 : Vertex.x cert (some (Vertex.i1 cert)) ∈ K
        · have hY0 (q : Fin (s - 1))
              (hqK : Vertex.y cert (some q) ∈ K) :
              q ∈ ({Certificates.i0Index' cert.five_le_s} :
                Finset (Fin (s - 1))) := by
            have hqi1 : q ≠ Vertex.i1 cert := by
              intro hq
              have hadj := hK.isClique hx1 hqK (by
                simp [Vertex.x, Vertex.y, hq])
              exact (blue_adj_x_y_iff cert _ _).1 hadj
                (congrArg some hq.symm)
            have hq1 : q.val ≠ 1 := by
              intro h
              apply hqi1
              apply Fin.ext
              simpa [Vertex.i1] using h
            have hq0 :
                q = Certificates.i0Index' cert.five_le_s := by
              apply Fin.ext
              simp
              have := hYsmall q hqK
              omega
            simp [hq0]
          have hsub :
              K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
                (ySet cert
                  {Certificates.i0Index' cert.five_le_s}) := by
            intro w hw
            rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
            · exact False.elim (ha0 (by simpa [hwa] using hw))
            · simpa [hwx]
            · exact Finset.mem_insert_of_mem ((mem_ySet cert _ q).2 (hY0 q hw))
          have hcard := card_le_one_add_ySet
            (cert := cert) (e := Vertex.x cert (some (Vertex.i1 cert)))
            (Q := {Certificates.i0Index' cert.five_le_s}) hsub
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          simp at hcard
          omega
        · let Qsmall : Finset (Fin (s - 1)) :=
            {Certificates.i0Index' cert.five_le_s,
              Vertex.i1 cert}
          have hYQ (q : Fin (s - 1))
              (hqK : Vertex.y cert (some q) ∈ K) : q ∈ Qsmall := by
            have hq := hYsmall q hqK
            have hqi :
                q = Certificates.i0Index' cert.five_le_s ∨
                  q = Vertex.i1 cert := by
              by_cases hq0 : q.val = 0
              · left
                apply Fin.ext
                simpa using hq0
              · right
                apply Fin.ext
                simp [Vertex.i1]
                omega
            simpa [Qsmall] using hqi
          have hsub : K ⊆ ySet cert Qsmall := by
            intro w hw
            rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
            · exact False.elim (ha0 (by simpa [hwa] using hw))
            · exact False.elim (hx1 (by simpa [hwx] using hw))
            · exact (mem_ySet cert Qsmall q).2 (hYQ q hw)
          have hcard := card_le_ySet hsub
          have hQ : Qsmall.card ≤ 2 := by
            simpa [Qsmall] using
              (Finset.card_insert_le
                (Certificates.i0Index' cert.five_le_s)
                ({Vertex.i1 cert} : Finset (Fin (s - 1))))
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          omega
      · have hYlarge (q : Fin (s - 1))
            (hqK : Vertex.y cert (some q) ∈ K) :
            q ∈ cert.largeIndices :=
          (cert.mem_largeIndices_iff q).2 (by
            by_contra hq
            exact hsmall ⟨q, hqK, by omega⟩)
        have hsub :
            K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
              (ySet cert cert.largeIndices) := by
          intro w hw
          rcases hclass hw with hwa | hwx | ⟨q, rfl⟩
          · exact False.elim (ha0 (by simpa [hwa] using hw))
          · simpa [hwx]
          · exact Finset.mem_insert_of_mem ((mem_ySet cert _ q).2 (hYlarge q hw))
        have hcard := card_le_one_add_ySet
          (cert := cert) (e := Vertex.x cert (some (Vertex.i1 cert)))
          (Q := cert.largeIndices) hsub
        have hcardLarge := cert.card_largeIndices
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega

private theorem blue_adj_b0_core_iff
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) (Vertex.core v) ↔
      v = cert.c (Vertex.c0 cert) ∨
        Gᶜ.Adj (cert.c (Vertex.c0 cert)) v := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.b, Vertex.core, Vertex.c0, redJoinedClone]
  tauto

private theorem blue_adj_ySome_core_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (v : V) :
    (BlueGraph cert).Adj (Vertex.y cert (some q)) (Vertex.core v) ↔
      Gᶜ.Adj (cert.i q) v := by
  rw [(BlueGraph cert).adj_comm]
  have hpre := pre_blue_adj_lower_y_iff cert
    (SpecialLiftVertex.core v) (some q)
  simp [Canonical.secondCertificateAt] at hpre
  rw [final_compl_adj_iff]
  simp [removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    hpre, Vertex.y, Vertex.core]

private theorem blue_adj_b0_b_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (BlueGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.b p) ↔ 3 ≤ p.val := by
  have hk := cert.five_le_k
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.b, Vertex.c0, Vertex.c2, SameBPart, redJoinedClone,
    Certificates.c0Index, Certificates.c2Index,
    Certificates.indexZero, Fin.mk.injEq]
  have h0 :
      ((⟨0, by omega⟩ : Fin (k - 1)) = p) ↔ p.val = 0 := by
    constructor
    · intro h
      simpa using congrArg Fin.val h.symm
    · intro h
      apply Fin.ext
      simpa using h.symm
  have h2 :
      (p = (⟨2, by omega⟩ : Fin (k - 1))) ↔ p.val = 2 := by
    constructor
    · intro h
      simpa using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa using h
  simp [h0, h2]
  omega

private theorem blue_adj_ySome_b_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (BlueGraph cert).Adj (Vertex.y cert (some q)) (Vertex.b p) ↔
      Gᶜ.Adj (cert.i q) (cert.c p) ∨
        (q ∈ cert.T ∧ p = Vertex.c0 cert) := by
  rw [(BlueGraph cert).adj_comm]
  have hpre := pre_blue_adj_lower_y_iff cert
    (SpecialLiftVertex.b p) (some q)
  have hci := cert.c_ne_i p q
  simp [Canonical.secondCertificateAt, hci, ne_comm] at hpre
  rw [final_compl_adj_iff]
  simp [removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    hpre, Vertex.y, Vertex.b,
    Certificates.OrderedCertificates.mem_T, or_comm, and_comm]
  tauto

private theorem common_b0_ySome_cases
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)} (hqT : q ∈ cert.T)
    {w : Vertex V k s}
    (hb : (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w)
    (hy : (BlueGraph cert).Adj (Vertex.y cert (some q)) w) :
    (∃ v : V, w = Vertex.core v ∧
      Gᶜ.Adj (cert.c (Vertex.c0 cert)) v ∧
      Gᶜ.Adj (cert.i q) v) ∨
    (∃ p : Fin (k - 1), w = Vertex.b p ∧ 3 ≤ p.val ∧
      Gᶜ.Adj (cert.i q) (cert.c p)) ∨
    (w = Vertex.x cert (some (Vertex.i1 cert)) ∧
      q ≠ Vertex.i1 cert) ∨
    w = Vertex.x cert none ∨
    ∃ r : Fin (s - 1), w = Vertex.y cert (some r) ∧ r ≠ q := by
  rcases w with w | u
  · rcases w with w | r | r
    · rcases w with v | p | p
      · left
        have hvq := (blue_adj_ySome_core_iff cert q v).1 hy
        rcases (blue_adj_b0_core_iff cert v).1 hb with hv0 | hv0
        · subst v
          exact False.elim
            (((SimpleGraph.compl_adj G _ _).1 hvq).2
              (G.adj_symm ((cert.mem_T q).1 hqT)))
        · exact ⟨v, rfl, hv0, hvq⟩
      ·
        have hp : p = Vertex.c0 cert := by
          simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
            removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
            Vertex.b, Vertex.a, Vertex.c0, redJoinedClone] using hb
        subst p
        have hqU :=
          (blue_adj_a0_ySome_iff cert q).1 ((BlueGraph cert).adj_symm hy)
        exact False.elim (((cert.mem_U q).1 hqU) hqT)
      · right; left
        have hp3 := (blue_adj_b0_b_iff cert p).1 hb
        rcases (blue_adj_ySome_b_iff cert q p).1 hy with hip | hswitch
        · exact ⟨p, rfl, hp3, hip⟩
        · have hp0 := congrArg Fin.val hswitch.2
          simp [Vertex.c0, Certificates.c0Index] at hp0
          omega
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hy ⊢
      cases o with
      | none =>
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | some t =>
          have ht :
              t = Vertex.i1 cert :=
            (blue_adj_xSome_b_iff cert t (Vertex.c0 cert)).1
              ((BlueGraph cert).adj_symm hb) |>.1
          subst t
          right; right; left
          refine ⟨rfl, ?_⟩
          have hne :
              (some (Vertex.i1 cert) : Option (Fin (s - 1))) ≠ some q :=
            (blue_adj_x_y_iff cert _ _).1 ((BlueGraph cert).adj_symm hy)
          intro hq
          exact hne (congrArg some hq.symm)
    ·
      generalize ho : Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r = o
      have hr : r = (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm o := by
        rw [← ho]
        simp
      rw [hr] at hb hy ⊢
      cases o with
      | none =>
          exact False.elim (by
            simpa [BlueGraph, finalGraph, preGraph, canonicalGraph,
              Canonical.graph, removedRedGraph, removedRedRel,
              addedRedGraph, addedRedRel, Vertex.b, Vertex.y,
              Vertex.c0, redJoinedClone] using hb)
      | some t =>
          right; right; right; right
          refine ⟨t, rfl, ?_⟩
          exact (blue_adj_ySome_ySome_iff cert q t).1 hy |>.1.symm
  ·
    exact False.elim (by
      simpa [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
        removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
        Vertex.b, Vertex.c0, redJoinedClone] using hb)

private noncomputable def b1Projection
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → V
  | .inl (.core (.core v)) => v
  | .inl (.core (.b p)) => cert.c p
  | .inl (.b r) =>
      match Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s)) r with
      | some q => cert.i q
      | none => cert.c (Vertex.c0 cert)
  | _ => cert.c (Vertex.c0 cert)

@[simp]
private theorem b1Projection_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    b1Projection cert (Vertex.core v) = v :=
  rfl

@[simp]
private theorem b1Projection_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    b1Projection cert (Vertex.b p) = cert.c p :=
  rfl

@[simp]
private theorem b1Projection_ySome
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    b1Projection cert (Vertex.y cert (some q)) = cert.i q := by
  simp [b1Projection, Vertex.y]

private theorem blue_adj_b_core_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) (v : V) :
    (BlueGraph cert).Adj (Vertex.b p) (Vertex.core v) ↔
      v = cert.c p ∨ Gᶜ.Adj (cert.c p) v := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.b, Vertex.core, Vertex.c0, redJoinedClone]
  tauto

private theorem blue_adj_core_core_iff
    (cert : Certificates.OrderedCertificates G k s) (u v : V) :
    (BlueGraph cert).Adj (Vertex.core u) (Vertex.core v) ↔
      Gᶜ.Adj u v := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.core, redJoinedClone]
  tauto

private theorem not_blue_adj_b_b_of_three_le
    (cert : Certificates.OrderedCertificates G k s)
    (p r : Fin (k - 1)) (hp : 3 ≤ p.val) (hr : 3 ≤ r.val) :
    ¬(BlueGraph cert).Adj (Vertex.b p) (Vertex.b r) := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.b, Vertex.c0, Vertex.c2, SameBPart, redJoinedClone,
    Certificates.c0Index, Certificates.indexZero, Fin.mk.injEq]
  omega

private theorem b1_card_succ_lt_of_no_x
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqT : q ∈ cert.T)
    {K : Finset (Vertex V k s)}
    (hcommon : ∀ {w : Vertex V k s}, w ∈ K →
      (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w ∧
      (BlueGraph cert).Adj (Vertex.y cert (some q)) w)
    (hK : (BlueGraph cert).IsClique (K : Set (Vertex V k s)))
    (hnoX : ∀ r : Option (Fin (s - 1)), Vertex.x cert r ∉ K) :
    K.card + 1 < s := by
  classical
  have hclass {w : Vertex V k s} (hw : w ∈ K) :
      (∃ v : V, w = Vertex.core v ∧
        Gᶜ.Adj (cert.c (Vertex.c0 cert)) v ∧
        Gᶜ.Adj (cert.i q) v) ∨
      (∃ p : Fin (k - 1), w = Vertex.b p ∧ 3 ≤ p.val ∧
        Gᶜ.Adj (cert.i q) (cert.c p)) ∨
      ∃ r : Fin (s - 1),
        w = Vertex.y cert (some r) ∧ r ≠ q := by
    rcases common_b0_ySome_cases cert hqT
        (hcommon hw).1 (hcommon hw).2 with
      hcore | hb | hx1 | hxstar | hy
    · exact Or.inl hcore
    · exact Or.inr (Or.inl hb)
    · exact False.elim
        (hnoX (some (Vertex.i1 cert)) (by simpa [hx1.1] using hw))
    · exact False.elim (hnoX none (by simpa [hxstar] using hw))
    · exact Or.inr (Or.inr hy)
  have hproj_inj :
      Set.InjOn (b1Projection cert) (K : Set (Vertex V k s)) := by
    intro u hu v hv huv
    rcases hclass hu with
      ⟨a, rfl, ha0, haq⟩ |
      ⟨p, rfl, hp3, hpq⟩ |
      ⟨r, rfl, hrq⟩ <;>
    rcases hclass hv with
      ⟨b, rfl, hb0, hbq⟩ |
      ⟨t, rfl, ht3, htq⟩ |
      ⟨z, rfl, hzq⟩
    · simpa using huv
    ·
      have hab : a = cert.c t := by simpa using huv
      subst a
      have h0t : Vertex.c0 cert ≠ t := by
        intro h
        have := congrArg Fin.val h
        simp [Vertex.c0, Certificates.c0Index] at this
        omega
      exact False.elim
        (((SimpleGraph.compl_adj G _ _).1 ha0).2 (cert.c_adj h0t))
    ·
      have haz : a = cert.i z := by simpa using huv
      subst a
      have hadj := hK hu hv (by simp [Vertex.core, Vertex.y])
      have hloop :
          Gᶜ.Adj (cert.i z) (cert.i z) :=
        (blue_adj_ySome_core_iff cert z (cert.i z)).1
          ((BlueGraph cert).adj_symm hadj)
      exact False.elim (Gᶜ.loopless.irrefl _ hloop)
    ·
      have hpa : cert.c p = b := by simpa using huv
      subst b
      have h0p : Vertex.c0 cert ≠ p := by
        intro h
        have := congrArg Fin.val h
        simp [Vertex.c0, Certificates.c0Index] at this
        omega
      exact False.elim
        (((SimpleGraph.compl_adj G _ _).1 hb0).2 (cert.c_adj h0p))
    ·
      have hpt : p = t := cert.c.injective (by simpa using huv)
      simpa [hpt]
    ·
      exact False.elim (cert.c_ne_i p z (by simpa using huv))
    ·
      have hzr : cert.i r = b := by simpa using huv
      subst b
      have hadj := hK hu hv (by simp [Vertex.core, Vertex.y])
      have hloop :
          Gᶜ.Adj (cert.i r) (cert.i r) :=
        (blue_adj_ySome_core_iff cert r (cert.i r)).1 hadj
      exact False.elim (Gᶜ.loopless.irrefl _ hloop)
    ·
      exact False.elim (cert.c_ne_i t r (by simpa using huv.symm))
    ·
      have hrz : r = z := cert.i.injective (by simpa using huv)
      simpa [hrz]
  have hproj_ne_iq {w : Vertex V k s} (hw : w ∈ K) :
      b1Projection cert w ≠ cert.i q := by
    rcases hclass hw with
      ⟨v, rfl, hv0, hvq⟩ |
      ⟨p, rfl, hp3, hpq⟩ |
      ⟨r, rfl, hrq⟩
    · intro hv
      have hv' : v = cert.i q := by simpa using hv
      rw [hv'] at hvq
      exact Gᶜ.loopless.irrefl _ hvq
    · simpa using cert.c_ne_i p q
    · intro h
      exact hrq (cert.i.injective (by simpa using h))
  have hproj_adj {u v : Vertex V k s}
      (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) :
      Gᶜ.Adj (b1Projection cert u) (b1Projection cert v) := by
    rcases hclass hu with
      ⟨a, rfl, ha0, haq⟩ |
      ⟨p, rfl, hp3, hpq⟩ |
      ⟨r, rfl, hrq⟩ <;>
    rcases hclass hv with
      ⟨b, rfl, hb0, hbq⟩ |
      ⟨t, rfl, ht3, htq⟩ |
      ⟨z, rfl, hzq⟩
    ·
      simpa using
        (blue_adj_core_core_iff cert a b).1 (hK hu hv huv)
    ·
      have hadj := hK hu hv huv
      rcases (blue_adj_b_core_iff cert t a).1
          ((BlueGraph cert).adj_symm hadj) with hat | hat
      ·
        subst a
        have h0t : Vertex.c0 cert ≠ t := by
          intro h
          have := congrArg Fin.val h
          simp [Vertex.c0, Certificates.c0Index] at this
          omega
        exact False.elim
          (((SimpleGraph.compl_adj G _ _).1 ha0).2 (cert.c_adj h0t))
      · simpa using Gᶜ.adj_symm hat
    ·
      have hadj := hK hu hv huv
      have hblue :=
        (blue_adj_ySome_core_iff cert z a).1
          ((BlueGraph cert).adj_symm hadj)
      simpa using Gᶜ.adj_symm hblue
    ·
      have hadj := hK hu hv huv
      rcases (blue_adj_b_core_iff cert p b).1 hadj with hbp | hbp
      ·
        subst b
        have h0p : Vertex.c0 cert ≠ p := by
          intro h
          have := congrArg Fin.val h
          simp [Vertex.c0, Certificates.c0Index] at this
          omega
        exact False.elim
          (((SimpleGraph.compl_adj G _ _).1 hb0).2 (cert.c_adj h0p))
      · simpa using hbp
    ·
      exact False.elim
        (not_blue_adj_b_b_of_three_le cert p t hp3 ht3 (hK hu hv huv))
    ·
      have hadj := hK hu hv huv
      rcases (blue_adj_ySome_b_iff cert z p).1
          ((BlueGraph cert).adj_symm hadj) with hzp | hswitch
      · simpa using Gᶜ.adj_symm hzp
      ·
        have hp0 := congrArg Fin.val hswitch.2
        simp [Vertex.c0, Certificates.c0Index] at hp0
        omega
    ·
      have hadj := hK hu hv huv
      simpa using (blue_adj_ySome_core_iff cert r b).1 hadj
    ·
      have hadj := hK hu hv huv
      rcases (blue_adj_ySome_b_iff cert r t).1 hadj with hrt | hswitch
      · simpa using hrt
      ·
        have ht0 := congrArg Fin.val hswitch.2
        simp [Vertex.c0, Certificates.c0Index] at ht0
        omega
    ·
      have hrz :=
        (blue_adj_ySome_ySome_iff cert r z).1 (hK hu hv huv) |>.1
      simpa using cert.i_compl_adj hrz
  have hproj_iq_adj {w : Vertex V k s} (hw : w ∈ K) :
      Gᶜ.Adj (b1Projection cert w) (cert.i q) := by
    rcases hclass hw with
      ⟨v, rfl, hv0, hvq⟩ |
      ⟨p, rfl, hp3, hpq⟩ |
      ⟨r, rfl, hrq⟩
    · simpa using Gᶜ.adj_symm hvq
    · simpa using Gᶜ.adj_symm hpq
    · simpa using cert.i_compl_adj hrq
  let f : ({w // w ∈ K} ⊕ Unit) ↪ V :=
    { toFun := fun x =>
        match x with
        | Sum.inl w => b1Projection cert w.1
        | Sum.inr _ => cert.i q
      inj' := by
        intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · apply congrArg Sum.inl
          apply Subtype.ext
          exact hproj_inj x.property y.property hxy
        · exact False.elim (hproj_ne_iq x.property hxy)
        · exact False.elim (hproj_ne_iq y.property hxy.symm)
        · exact congrArg Sum.inr (Subsingleton.elim x y) }
  have hfclique :
      ∀ x y : ({w // w ∈ K} ⊕ Unit), x ≠ y →
        Gᶜ.Adj (f x) (f y) := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    ·
      apply hproj_adj x.property y.property
      intro huv
      apply hxy
      apply congrArg Sum.inl
      apply Subtype.ext
      exact huv
    · exact hproj_iq_adj x.property
    · exact Gᶜ.adj_symm (hproj_iq_adj y.property)
    · exact False.elim
        (hxy (congrArg Sum.inr (Subsingleton.elim x y)))
  have hlt := card_lt_of_cliqueFree_of_embedding hG.2 f hfclique
  simpa using hlt

private theorem b1_y_index_of_large
    (cert : Certificates.OrderedCertificates G k s)
    {q r : Fin (s - 1)} (hq2 : 2 ≤ q.val)
    (hqr : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some r))) :
    r = Vertex.i1 cert ∨ r ∈ cert.largeIndices.erase q := by
  rcases (blue_adj_ySome_ySome_iff cert q r).1 hqr with
    ⟨hrq, hpart | hswitch | hswitch⟩
  · right
    have hs :
        (q.val < 2 ∧ r.val < 2) ∨
          (2 ≤ q.val ∧ 2 ≤ r.val) := by
      simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
    have hr2 : 2 ≤ r.val := by
      rcases hs with hs | hs <;> omega
    exact Finset.mem_erase.2
      ⟨Ne.symm hrq, (cert.mem_largeIndices_iff r).2 hr2⟩
  ·
    have hqv := congrArg Fin.val hswitch.1
    simp [Vertex.i1] at hqv
    omega
  · exact Or.inl hswitch.1

private theorem b1_y_index_of_one
    (cert : Certificates.OrderedCertificates G k s)
    {q r : Fin (s - 1)} (hq1 : q.val = 1)
    (hqr : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some r))) :
    r = Certificates.i0Index' cert.five_le_s ∨
      r ∈ cert.ELarge := by
  have hqi1 : q = Vertex.i1 cert := by
    apply Fin.ext
    simpa [Vertex.i1] using hq1
  rcases (blue_adj_ySome_ySome_iff cert q r).1 hqr with
    ⟨hrq, hpart | hswitch | hswitch⟩
  · left
    have hs :
        (q.val < 2 ∧ r.val < 2) ∨
          (2 ≤ q.val ∧ 2 ≤ r.val) := by
      simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
    apply Fin.ext
    simp
    have hrne1 : r.val ≠ 1 := by
      intro hr1
      apply hrq
      apply Fin.ext
      omega
    rcases hs with hs | hs <;> omega
  · right
    exact (cert.mem_ELarge r).2 ⟨hswitch.2.1, hswitch.2.2⟩
  · exact False.elim (hrq (hqi1.trans hswitch.1.symm))

private theorem b1_y_index_of_zero
    (cert : Certificates.OrderedCertificates G k s)
    {q r : Fin (s - 1)} (hq0 : q.val = 0)
    (hqr : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some r))) :
    r = Vertex.i1 cert := by
  rcases (blue_adj_ySome_ySome_iff cert q r).1 hqr with
    ⟨hrq, hpart | hswitch | hswitch⟩
  ·
    have hs :
        (q.val < 2 ∧ r.val < 2) ∨
          (2 ≤ q.val ∧ 2 ≤ r.val) := by
      simpa [Canonical.outerIndexEquiv, SameBPart] using hpart
    apply Fin.ext
    simp [Vertex.i1]
    have hrne0 : r.val ≠ 0 := by
      intro hr0
      apply hrq
      apply Fin.ext
      omega
    rcases hs with hs | hs <;> omega
  ·
    have hqv := congrArg Fin.val hswitch.1
    simp [Vertex.i1] at hqv
    omega
  · exact hswitch.1

/-- Row (B1): every switched edge `b₀y_q`, with `q ∈ T`, is blue-safe. -/
theorem blue_case_b1
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqT : q ∈ cert.T) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q))) (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj (Vertex.b (Vertex.c0 cert)) w ∧
        (BlueGraph cert).Adj (Vertex.y cert (some q)) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hclass {w : Vertex V k s} (hw : w ∈ K) :=
    common_b0_ySome_cases cert hqT (hcommon hw).1 (hcommon hw).2
  have hstar_class
      (hxstar : Vertex.x cert none ∈ K)
      {w : Vertex V k s} (hw : w ∈ K) :
      (w = Vertex.x cert (some (Vertex.i1 cert)) ∧
        q ≠ Vertex.i1 cert) ∨
      w = Vertex.x cert none ∨
      ∃ r : Fin (s - 1),
        w = Vertex.y cert (some r) ∧ r ≠ q := by
    rcases hclass hw with hcore | hb | hx1 | hxstar' | hy
    · obtain ⟨v, rfl, hv0, hvq⟩ := hcore
      have hadj := hK.isClique hxstar hw (by
        simp [Vertex.x, Vertex.core])
      exact False.elim (not_blue_adj_xNone_core cert v hadj)
    · obtain ⟨p, rfl, hp3, hpq⟩ := hb
      have hadj := hK.isClique hxstar hw (by
        simp [Vertex.x, Vertex.b])
      have hp0 := (blue_adj_xNone_b_iff cert p).1 hadj
      have hpv := congrArg Fin.val hp0
      simp [Vertex.c0, Certificates.c0Index] at hpv
      omega
    · exact Or.inl hx1
    · exact Or.inr (Or.inl hxstar')
    · exact Or.inr (Or.inr hy)
  have hone_class
      (hx1 : Vertex.x cert (some (Vertex.i1 cert)) ∈ K)
      (hxstar : Vertex.x cert none ∉ K)
      {w : Vertex V k s} (hw : w ∈ K) :
      w = Vertex.core (cert.i (Vertex.i1 cert)) ∨
      w = Vertex.x cert (some (Vertex.i1 cert)) ∨
      ∃ r : Fin (s - 1),
        w = Vertex.y cert (some r) ∧ r ≠ q := by
    rcases hclass hw with hcore | hb | hx1' | hxstar' | hy
    · obtain ⟨v, rfl, hv0, hvq⟩ := hcore
      left
      have hadj := hK.isClique hx1 hw (by
        simp [Vertex.x, Vertex.core])
      have hv := (blue_adj_xSome_core_iff cert (Vertex.i1 cert) v).1 hadj
      simpa [hv]
    · obtain ⟨p, rfl, hp3, hpq⟩ := hb
      have hadj := hK.isClique hx1 hw (by
        simp [Vertex.x, Vertex.b])
      have hp0 :=
        (blue_adj_xSome_b_iff cert (Vertex.i1 cert) p).1 hadj |>.2
      have hpv := congrArg Fin.val hp0
      simp [Vertex.c0, Certificates.c0Index] at hpv
      omega
    · exact Or.inr (Or.inl hx1'.1)
    · exact False.elim (hxstar (by simpa [hxstar'] using hw))
    · exact Or.inr (Or.inr hy)
  have hELarge : cert.ELarge.card ≤ s - k := by
    by_cases hE : cert.E.Nonempty
    · obtain ⟨hB⟩ := (cert.E_nonempty_iff_caseB hG).1 hE
      exact cert.caseB_card_ELarge_le hB
    · have hEempty : cert.E = ∅ :=
        Finset.not_nonempty_iff_eq_empty.1 hE
      simp [Certificates.OrderedCertificates.ELarge, hEempty]
  by_cases hx1 : Vertex.x cert (some (Vertex.i1 cert)) ∈ K
  · have hq_ne_i1 : q ≠ Vertex.i1 cert := by
      have hne :
          (some (Vertex.i1 cert) : Option (Fin (s - 1))) ≠ some q :=
        (blue_adj_x_y_iff cert _ _).1
          ((BlueGraph cert).adj_symm (hcommon hx1).2)
      intro hq
      exact hne (congrArg some hq.symm)
    have hq_ne_one : q.val ≠ 1 := by
      intro hq1
      apply hq_ne_i1
      apply Fin.ext
      simpa [Vertex.i1] using hq1
    have hy_ne_i1 (r : Fin (s - 1))
        (hrK : Vertex.y cert (some r) ∈ K) :
        r ≠ Vertex.i1 cert := by
      intro hr
      have hadj := hK.isClique hx1 hrK (by
        simp [Vertex.x, Vertex.y, hr])
      exact (blue_adj_x_y_iff cert _ _).1 hadj
        (congrArg some hr.symm)
    by_cases hxstar : Vertex.x cert none ∈ K
    · by_cases hq0 : q.val = 0
      · have hsub :
            K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
              (insert (Vertex.x cert none) (ySet cert ∅)) := by
          intro w hw
          rcases hstar_class hxstar hw with hx1' | hxstar' | ⟨r, hwr, hrq⟩
          · simpa [hx1'.1]
          · simpa [hxstar']
          · subst w
            have hr1 := b1_y_index_of_zero cert hq0 (hcommon hw).2
            exact False.elim (hy_ne_i1 r hw hr1)
        have hcard := card_le_two_add_ySet
          (cert := cert)
          (e₁ := Vertex.x cert (some (Vertex.i1 cert)))
          (e₂ := Vertex.x cert none) (Q := ∅) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        simp at hcard
        omega
      · have hq2 : 2 ≤ q.val := by omega
        let Q : Finset (Fin (s - 1)) := cert.largeIndices.erase q
        have hqLarge : q ∈ cert.largeIndices :=
          (cert.mem_largeIndices_iff q).2 hq2
        have hQcard : Q.card = s - 4 := by
          dsimp [Q]
          rw [Finset.card_erase_of_mem hqLarge, cert.card_largeIndices]
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          omega
        have hsub :
            K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
              (insert (Vertex.x cert none) (ySet cert Q)) := by
          intro w hw
          rcases hstar_class hxstar hw with hx1' | hxstar' | ⟨r, hwr, hrq⟩
          · simpa [hx1'.1]
          · simpa [hxstar']
          · subst w
            rcases b1_y_index_of_large cert hq2 (hcommon hw).2 with hr1 | hrQ
            · exact False.elim (hy_ne_i1 r hw hr1)
            · exact Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem ((mem_ySet cert Q r).2 hrQ))
        have hcard := card_le_two_add_ySet
          (cert := cert)
          (e₁ := Vertex.x cert (some (Vertex.i1 cert)))
          (e₂ := Vertex.x cert none) (Q := Q) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega
    · by_cases hq0 : q.val = 0
      · have hsub :
            K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
              (insert (Vertex.core (cert.i (Vertex.i1 cert)))
                (ySet cert ∅)) := by
          intro w hw
          rcases hone_class hx1 hxstar hw with hcore | hx1' | ⟨r, hwr, hrq⟩
          · simpa [hcore]
          · simpa [hx1']
          · subst w
            have hr1 := b1_y_index_of_zero cert hq0 (hcommon hw).2
            exact False.elim (hy_ne_i1 r hw hr1)
        have hcard := card_le_two_add_ySet
          (cert := cert)
          (e₁ := Vertex.x cert (some (Vertex.i1 cert)))
          (e₂ := Vertex.core (cert.i (Vertex.i1 cert)))
          (Q := ∅) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        simp at hcard
        omega
      · have hq2 : 2 ≤ q.val := by omega
        let Q : Finset (Fin (s - 1)) := cert.largeIndices.erase q
        have hqLarge : q ∈ cert.largeIndices :=
          (cert.mem_largeIndices_iff q).2 hq2
        have hQcard : Q.card = s - 4 := by
          dsimp [Q]
          rw [Finset.card_erase_of_mem hqLarge, cert.card_largeIndices]
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          omega
        have hsub :
            K ⊆ insert (Vertex.x cert (some (Vertex.i1 cert)))
              (insert (Vertex.core (cert.i (Vertex.i1 cert)))
                (ySet cert Q)) := by
          intro w hw
          rcases hone_class hx1 hxstar hw with hcore | hx1' | ⟨r, hwr, hrq⟩
          · simpa [hcore]
          · simpa [hx1']
          · subst w
            rcases b1_y_index_of_large cert hq2 (hcommon hw).2 with hr1 | hrQ
            · exact False.elim (hy_ne_i1 r hw hr1)
            · exact Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem ((mem_ySet cert Q r).2 hrQ))
        have hcard := card_le_two_add_ySet
          (cert := cert)
          (e₁ := Vertex.x cert (some (Vertex.i1 cert)))
          (e₂ := Vertex.core (cert.i (Vertex.i1 cert)))
          (Q := Q) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        omega
  · by_cases hxstar : Vertex.x cert none ∈ K
    · by_cases hq0 : q.val = 0
      · let Q : Finset (Fin (s - 1)) := {Vertex.i1 cert}
        have hsub :
            K ⊆ insert (Vertex.x cert none) (ySet cert Q) := by
          intro w hw
          rcases hstar_class hxstar hw with hx1' | hxstar' | ⟨r, hwr, hrq⟩
          · exact False.elim (hx1 (by simpa [hx1'.1] using hw))
          · simpa [hxstar']
          · subst w
            exact Finset.mem_insert_of_mem
              ((mem_ySet cert Q r).2 (by
                simp [Q, b1_y_index_of_zero cert hq0 (hcommon hw).2]))
        have hcard := card_le_one_add_ySet
          (cert := cert) (e := Vertex.x cert none) (Q := Q) hsub
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hs5 := cert.five_le_s
        simp [Q] at hcard
        omega
      · by_cases hq1 : q.val = 1
        · let Q : Finset (Fin (s - 1)) :=
            insert (Certificates.i0Index' cert.five_le_s)
              cert.ELarge
          have hsub :
              K ⊆ insert (Vertex.x cert none) (ySet cert Q) := by
            intro w hw
            rcases hstar_class hxstar hw with hx1' | hxstar' | ⟨r, hwr, hrq⟩
            · exact False.elim (hx1 (by simpa [hx1'.1] using hw))
            · simpa [hxstar']
            · subst w
              rcases b1_y_index_of_one cert hq1 (hcommon hw).2 with hr0 | hrE
              · exact Finset.mem_insert_of_mem
                  ((mem_ySet cert Q r).2 (by simp [Q, hr0]))
              · exact Finset.mem_insert_of_mem
                  ((mem_ySet cert Q r).2 (by
                    exact Finset.mem_insert_of_mem hrE))
          have hcard := card_le_one_add_ySet
            (cert := cert) (e := Vertex.x cert none) (Q := Q) hsub
          have hQ : Q.card ≤ cert.ELarge.card + 1 := by
            exact Finset.card_insert_le _ _
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          omega
        · have hq2 : 2 ≤ q.val := by omega
          let Q : Finset (Fin (s - 1)) :=
            insert (Vertex.i1 cert) (cert.largeIndices.erase q)
          have hqLarge : q ∈ cert.largeIndices :=
            (cert.mem_largeIndices_iff q).2 hq2
          have hErase : (cert.largeIndices.erase q).card = s - 4 := by
            rw [Finset.card_erase_of_mem hqLarge, cert.card_largeIndices]
            have hk := cert.five_le_k
            have hs5 := cert.five_le_s
            omega
          have hsub :
              K ⊆ insert (Vertex.x cert none) (ySet cert Q) := by
            intro w hw
            rcases hstar_class hxstar hw with hx1' | hxstar' | ⟨r, hwr, hrq⟩
            · exact False.elim (hx1 (by simpa [hx1'.1] using hw))
            · simpa [hxstar']
            · subst w
              rcases b1_y_index_of_large cert hq2 (hcommon hw).2 with hr1 | hrQ
              · exact Finset.mem_insert_of_mem
                  ((mem_ySet cert Q r).2 (by simp [Q, hr1]))
              · exact Finset.mem_insert_of_mem
                  ((mem_ySet cert Q r).2 (by
                    exact Finset.mem_insert_of_mem hrQ))
          have hcard := card_le_one_add_ySet
            (cert := cert) (e := Vertex.x cert none) (Q := Q) hsub
          have hQ : Q.card ≤ (cert.largeIndices.erase q).card + 1 := by
            exact Finset.card_insert_le _ _
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hs5 := cert.five_le_s
          omega
    ·
      have hnoX (r : Option (Fin (s - 1))) :
          Vertex.x cert r ∉ K := by
        intro hrK
        rcases hclass hrK with hcore | hb | hx1' | hxstar' | hy
        · obtain ⟨v, heq, hv0, hvq⟩ := hcore
          simp [Vertex.x, Vertex.core] at heq
        · obtain ⟨p, heq, hp3, hpq⟩ := hb
          simp [Vertex.x, Vertex.b] at heq
        · apply hx1
          simpa [hx1'.1] using hrK
        · apply hxstar
          simpa [hxstar'] using hrK
        · obtain ⟨t, heq, htq⟩ := hy
          simp [Vertex.x, Vertex.y] at heq
      have hlt := b1_card_succ_lt_of_no_x cert hG hqT
        hcommon hK.isClique hnoX
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs5 := cert.five_le_s
      omega

end Switching
end RamseyIncrement
