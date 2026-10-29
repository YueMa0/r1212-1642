/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Construction

/-!
# Red dangerous-edge cases

This file formalizes rows (R1)--(R4) of the switching argument.
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

private abbrev hs (cert : Certificates.OrderedCertificates G k s) : 1 ≤ s :=
  le_trans (by decide : 1 ≤ 5)
    cert.five_le_s

@[simp]
private theorem secondCertificate_symm
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
        ((Canonical.outerIndexEquiv (hs cert)).symm r) =
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r := by
  rw [Canonical.secondCertificate_apply]
  simp

private theorem test_pre_b0_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
  simp only [preGraph, Vertex.b, Vertex.core, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa using
    (specialLift_adj_b_core G cert.c (Vertex.c0 cert) v)

private theorem test_pre_b0_a
    (cert : Certificates.OrderedCertificates G k s) (p : Fin (k - 1)) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.a p) ↔ p ≠ Vertex.c0 cert := by
  simp only [preGraph, Vertex.b, Vertex.a, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa [ne_comm] using
    (specialLift_adj_b_a G cert.c (Vertex.c0 cert) p)

private theorem test_pre_b0_b
    (cert : Certificates.OrderedCertificates G k s) (p : Fin (k - 1)) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.b p) ↔
        Vertex.c0 cert ≠ p ∧ SameBPart (Vertex.c0 cert) p := by
  simp only [preGraph, Vertex.b, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa using
    (specialLift_adj_b_b G cert.c (Vertex.c0 cert) p)

private theorem test_pre_b0_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.x cert r) ↔ True := by
  simp only [preGraph, Vertex.b, Vertex.x, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_a]
  change
    Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
        ((Canonical.outerIndexEquiv (hs cert)).symm r) ≠
        SpecialLiftVertex.b (Vertex.c0 cert) ↔ True
  rw [secondCertificate_symm]
  cases r with
  | none => simp [Canonical.secondCertificateAt]
  | some q =>
      simp [Canonical.secondCertificateAt,
        (cert.c_ne_i (Vertex.c0 cert) q).symm]

private theorem test_pre_b0_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.y cert r) ↔
        match r with
        | some q => G.Adj (cert.c (Vertex.c0 cert)) (cert.i q)
        | none => False := by
  simp only [preGraph, Vertex.b, Vertex.y, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_b]
  simp only [compl_compl]
  change
    SpecialLiftVertex.b (Vertex.c0 cert) =
          Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm r) ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm r))
          (SpecialLiftVertex.b (Vertex.c0 cert)) ↔
      match r with
      | some q => G.Adj (cert.c (Vertex.c0 cert)) (cert.i q)
      | none => False
  rw [secondCertificate_symm]
  cases r with
  | none => simp [Canonical.secondCertificateAt]
  | some q =>
      simp [Canonical.secondCertificateAt,
        (cert.c_ne_i (Vertex.c0 cert) q).symm]

private theorem test_final_b0_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, test_pre_b0_core]

private theorem test_final_z_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (finalGraph cert).Adj Vertex.z (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
  simp [finalGraph, preGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, canonicalGraph, Canonical.graph,
    Vertex.core, Vertex.b]

private theorem test_final_b0_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.a p) ↔
        p ≠ Vertex.c0 cert := by
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, test_pre_b0_a]

private theorem test_final_z_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj Vertex.z (Vertex.a p) ↔
        p ≠ Vertex.c0 cert := by
  simp [finalGraph, preGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, canonicalGraph, Canonical.graph,
    Vertex.a, Vertex.b]

private theorem test_final_b0_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.b p) ↔
        p = Vertex.c2 cert ∨
          (Vertex.c0 cert ≠ p ∧ SameBPart (Vertex.c0 cert) p) := by
  have h02 : Vertex.c0 cert ≠ Vertex.c2 cert := by
    intro h
    have hv := congrArg Fin.val h
    simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, test_pre_b0_b, h02]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.2
  · rintro (rfl | h)
    · exact Or.inr ⟨h02, rfl⟩
    · exact Or.inl h

private theorem test_final_z_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj Vertex.z (Vertex.b p) ↔
        p = Vertex.c0 cert ∨
          (Vertex.c0 cert ≠ p ∧ SameBPart (Vertex.c0 cert) p) := by
  simp [finalGraph, preGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, canonicalGraph, Canonical.graph,
    Vertex.b]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, (h.2 h.1).2⟩
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, fun hn ↦ ⟨hn, h.2⟩⟩

private theorem test_final_b0_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.x cert r) ↔
        r ≠ some (Vertex.i1 cert) ∧ r ≠ none := by
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, test_pre_b0_x]

private theorem test_final_z_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj Vertex.z (Vertex.x cert r) ↔
        r = some (Vertex.i1 cert) ∨ r = none := by
  have hpre :
      (preGraph cert).Adj Vertex.z (Vertex.x cert r) := by
    simp only [preGraph, Vertex.x, Vertex.b, redJoinedClone.adj_z_old]
    exact Or.inr ((test_pre_b0_x cert r).2 trivial)
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, hpre]
  cases r with
  | none => simp
  | some q =>
      by_cases hq : q = Vertex.i1 cert <;> simp [hq, ne_comm]

private theorem test_final_b0_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.y cert r) ↔ r = none := by
  cases r with
  | none =>
      simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
        addedRedRel, test_pre_b0_y]
  | some q =>
      have hpre :
        (preGraph cert).Adj
            (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
          q ∈ cert.T := by
        rw [test_pre_b0_y, cert.mem_T]
      rw [final_adj_iff, hpre]
      simp [removedRedGraph, removedRedRel, addedRedGraph, addedRedRel]

private theorem test_pre_z_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj Vertex.z (Vertex.y cert r) ↔
        match r with
        | some q => G.Adj (cert.c (Vertex.c0 cert)) (cert.i q)
        | none => False := by
  have hb := test_pre_b0_y cert r
  simp only [preGraph, Vertex.b, redJoinedClone.adj_old_old] at hb
  simp only [preGraph, Vertex.y, redJoinedClone.adj_z_old]
  rw [or_iff_right (by simp)]
  exact hb

private theorem test_final_z_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj Vertex.z (Vertex.y cert r) ↔
        ∃ q ∈ cert.T, r = some q := by
  cases r with
  | none =>
      rw [final_adj_iff]
      simp [test_pre_z_y, removedRedGraph, removedRedRel,
        addedRedGraph, addedRedRel]
  | some q =>
      have hpre :
          (preGraph cert).Adj Vertex.z (Vertex.y cert (some q)) ↔
            q ∈ cert.T := by
        rw [test_pre_z_y, cert.mem_T]
      rw [final_adj_iff, hpre]
      simp [removedRedGraph, removedRedRel, addedRedGraph, addedRedRel]

private theorem vertex_cases
    (cert : Certificates.OrderedCertificates G k s)
    (w : Vertex V k s) :
    (∃ v, w = Vertex.core v) ∨
      (∃ p, w = Vertex.a p) ∨
      (∃ p, w = Vertex.b p) ∨
      (∃ r, w = Vertex.x cert r) ∨
      (∃ r, w = Vertex.y cert r) ∨
      w = Vertex.z := by
  rcases w with w | _
  · cases w with
    | core w =>
        cases w with
        | core v => exact Or.inl ⟨v, rfl⟩
        | a p => exact Or.inr (Or.inl ⟨p, rfl⟩)
        | b p => exact Or.inr (Or.inr (Or.inl ⟨p, rfl⟩))
    | a r =>
        refine Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Canonical.outerIndexEquiv (hs cert) r, ?_⟩)))
        simp [Vertex.x]
    | b r =>
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Canonical.outerIndexEquiv (hs cert) r, ?_⟩))))
        simp [Vertex.y]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private def firstProjection
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → SpecialLiftVertex V k
  | .inl (.core w) => w
  | _ => .b (Vertex.c0 cert)

@[simp]
private theorem firstProjection_core
    (cert : Certificates.OrderedCertificates G k s)
    (w : SpecialLiftVertex V k) :
    firstProjection cert (.inl (.core w)) = w :=
  rfl

private theorem mem_common_b0_z_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w : Vertex V k s) :
    w ∈ (finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) Vertex.z ↔
      ∃ d : SpecialLiftVertex V k,
        w = .inl (.core d) ∧
          (specialLift G cert.c).Adj
            (.b (Vertex.c0 cert)) d := by
  rw [SimpleGraph.mem_commonNeighbors]
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    simp [test_final_b0_core, test_final_z_core]
  · obtain ⟨p, rfl⟩ := h
    simp [test_final_b0_a, test_final_z_a, ne_comm]
  · obtain ⟨p, rfl⟩ := h
    rw [test_final_b0_b, test_final_z_b]
    simp only [Sum.inl.injEq, SpecialLiftVertex.core.injEq,
      exists_eq_left', specialLift_adj_b_b]
    have h02 : Vertex.c0 cert ≠ Vertex.c2 cert := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
    have hpart02 :
        ¬SameBPart (Vertex.c0 cert) (Vertex.c2 cert) := by
      simp [SameBPart, Vertex.c0, Vertex.c2, Certificates.c0Index]
    constructor
    · rintro ⟨h0 | hold, hz⟩
      · subst p
        exact False.elim <| hz.elim h02.symm (fun h ↦ hpart02 h.2)
      · exact hold
    · intro hold
      exact ⟨Or.inr hold, Or.inr hold⟩
  · obtain ⟨r, rfl⟩ := h
    simp [test_final_b0_x, test_final_z_x]
  · obtain ⟨r, rfl⟩ := h
    cases r <;> simp [test_final_b0_y, test_final_z_y]
  · subst w
    simp

private theorem final_adj_projects_on_common_b0_z
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (hu : u ∈ (finalGraph cert).commonNeighbors
      (Vertex.b (Vertex.c0 cert)) Vertex.z)
    (hv : v ∈ (finalGraph cert).commonNeighbors
      (Vertex.b (Vertex.c0 cert)) Vertex.z)
    (huv : (finalGraph cert).Adj u v) :
    (specialLift G cert.c).Adj
      (firstProjection cert u) (firstProjection cert v) := by
  obtain ⟨d, rfl, hd⟩ := (mem_common_b0_z_iff cert u).1 hu
  obtain ⟨e, rfl, he⟩ := (mem_common_b0_z_iff cert v).1 hv
  simp only [firstProjection_core]
  rw [final_adj_iff] at huv
  rcases huv with huv | huv
  · have hp := huv.1
    simp [preGraph, canonicalGraph, Canonical.graph] at hp
    exact hp.2 hp.1
  · simp [addedRedGraph, addedRedRel] at huv
    rcases huv.2 with h | h
    · rcases h with ⟨hdb, heb⟩
      subst d
      subst e
      exact False.elim ((specialLift G cert.c).loopless.irrefl _ hd)
    · rcases h with ⟨hdb, heb⟩
      subst d
      subst e
      exact False.elim ((specialLift G cert.c).loopless.irrefl _ he)

/-- Row (R1): the clone-source edge `b₀z` cannot be extended to a red
`K_(k+1)` in the final graph. -/
theorem red_safe_b0_z
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    (finalGraph cert).CliqueFreeOn
      ((finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) Vertex.z)
      (k - 1) := by
  classical
  intro t htcommon ht
  let p : Finset (SpecialLiftVertex V k) :=
    t.image (firstProjection cert)
  have hinj :
      Set.InjOn (firstProjection cert) t := by
    intro u hu v hv huv
    obtain ⟨d, rfl, -⟩ :=
      (mem_common_b0_z_iff cert u).1 (htcommon hu)
    obtain ⟨e, rfl, -⟩ :=
      (mem_common_b0_z_iff cert v).1 (htcommon hv)
    simpa using huv
  have hpClique : (specialLift G cert.c).IsClique (p : Set _) := by
    intro d hd e he hde
    obtain ⟨u, hut, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨v, hvt, rfl⟩ := Finset.mem_image.mp he
    apply final_adj_projects_on_common_b0_z cert
      (htcommon hut) (htcommon hvt)
    apply ht.isClique hut hvt
    intro huv
    subst v
    exact hde rfl
  have hb0not :
      (SpecialLiftVertex.b (Vertex.c0 cert) : SpecialLiftVertex V k) ∉ p := by
    intro hb
    obtain ⟨u, hut, hu⟩ := Finset.mem_image.mp hb
    obtain ⟨d, rfl, hd⟩ :=
      (mem_common_b0_z_iff cert u).1 (htcommon hut)
    simp only [firstProjection_core] at hu
    subst d
    exact (specialLift G cert.c).loopless.irrefl _ hd
  have hbigClique :
      (specialLift G cert.c).IsClique
        (↑(insert
          (SpecialLiftVertex.b (Vertex.c0 cert)) p) : Set _) := by
    rw [Finset.coe_insert]
    exact hpClique.insert fun d hd _ ↦ by
      obtain ⟨u, hut, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨e, rfl, he⟩ :=
        (mem_common_b0_z_iff cert u).1 (htcommon hut)
      simpa using he
  have hpCard : p.card = k - 1 := by
    rw [Finset.card_image_of_injOn hinj, ht.card_eq]
  have hbigCard :
      (insert
        (SpecialLiftVertex.b (Vertex.c0 cert)) p).card = k := by
    rw [Finset.card_insert_of_notMem hb0not, hpCard]
    have hk := cert.five_le_k
    omega
  exact
    (specialLift_cliqueFree G cert.c cert.c_isClique
      cert.five_le_k hG.1)
      _ ⟨hbigClique, hbigCard⟩

private theorem pre_ystar_first
    (cert : Certificates.OrderedCertificates G k s)
    (d : SpecialLiftVertex V k) :
    (preGraph cert).Adj (Vertex.y cert none) (.inl (.core d)) ↔
      d = .a (Vertex.c0 cert) ∨
        (specialLift G cert.c).Adj (.a (Vertex.c0 cert)) d := by
  simp only [preGraph, Vertex.y, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_b_core]
  simp only [compl_compl]
  change
    d =
          Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm none) ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm none)) d ↔
      d = .a (Vertex.c0 cert) ∨
        (specialLift G cert.c).Adj (.a (Vertex.c0 cert)) d
  rw [secondCertificate_symm]
  rfl

private theorem final_ystar_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (finalGraph cert).Adj (Vertex.y cert none) (Vertex.core v) ↔
      v = cert.c (Vertex.c0 cert) := by
  rw [final_adj_iff]
  simp [pre_ystar_first, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel]
  exact eq_comm

private theorem final_ystar_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj (Vertex.y cert none) (Vertex.a p) := by
  rw [final_adj_iff]
  left
  constructor
  · rw [pre_ystar_first]
    by_cases hp : p = Vertex.c0 cert
    · exact Or.inl (by simpa [hp])
    · exact Or.inr ((specialLift_adj_a_a G cert.c
        (Vertex.c0 cert) p).2 (Ne.symm hp))
  · simp [removedRedGraph, removedRedRel]

private theorem final_ystar_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj (Vertex.y cert none) (Vertex.b p) := by
  rw [final_adj_iff]
  by_cases hp : p = Vertex.c0 cert
  · subst p
    right
    simp [addedRedGraph, addedRedRel]
  · left
    constructor
    · rw [pre_ystar_first]
      exact Or.inr ((specialLift_adj_a_b G cert.c
        (Vertex.c0 cert) p).2 (Ne.symm hp))
    · simp [removedRedGraph, removedRedRel]

private theorem final_ystar_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj (Vertex.y cert none) (Vertex.x cert r) ↔
      r = none := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph, Vertex.y, Vertex.x,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel]

private abbrev c1
    (cert : Certificates.OrderedCertificates G k s) : Fin (k - 1) :=
  Certificates.c1Index cert.five_le_k

private theorem mem_common_b0_ystar_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w : Vertex V k s) :
    w ∈ (finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.y cert none) ↔
      (∃ p, p ≠ Vertex.c0 cert ∧ w = Vertex.a p) ∨
        w = Vertex.b (c1 cert) ∨
        w = Vertex.b (Vertex.c2 cert) := by
  rw [SimpleGraph.mem_commonNeighbors]
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    rw [test_final_b0_core, final_ystar_core]
    simp
    tauto
  · obtain ⟨p, rfl⟩ := h
    rw [test_final_b0_a]
    simp only [final_ystar_a, true_and]
    aesop
  · obtain ⟨p, rfl⟩ := h
    rw [test_final_b0_b]
    simp only [final_ystar_b, and_true]
    have hsame :
        Vertex.c0 cert ≠ p ∧ SameBPart (Vertex.c0 cert) p ↔
          p = c1 cert := by
      constructor
      · rintro ⟨hp0, hp⟩
        apply Fin.ext
        rcases hp with hp | hp
        · simp [Vertex.c0, c1, Certificates.c0Index,
            Certificates.c1Index] at hp ⊢
          have hpval : p.val ≠ 0 := by
            intro hpv
            apply hp0
            apply Fin.ext
            simpa [Vertex.c0, Certificates.c0Index] using hpv.symm
          omega
        · simp [Vertex.c0, Certificates.c0Index] at hp
      · rintro rfl
        constructor
        · exact Certificates.c0_ne_c1 cert.five_le_k
        · exact Or.inl (by
            simp [Vertex.c0, c1, Certificates.c0Index,
              Certificates.c1Index])
    rw [hsame]
    constructor
    · intro hp
      rcases hp with hp | hp
      · exact Or.inr (Or.inr (by simpa [hp]))
      · exact Or.inr (Or.inl (by simpa [hp]))
    · intro hp
      rcases hp with hp | hp | hp
      · obtain ⟨_, _, hfalse⟩ := hp
        simp at hfalse
      · exact Or.inr (by simpa using hp)
      · exact Or.inl (by simpa using hp)
  · obtain ⟨r, rfl⟩ := h
    rw [test_final_b0_x, final_ystar_x]
    simp
  · obtain ⟨r, rfl⟩ := h
    rw [test_final_b0_y]
    cases r with
    | none => simp
    | some q => simp
  · subst w
    have hyz :
        ¬(finalGraph cert).Adj (Vertex.y cert none) Vertex.z := by
      rw [(finalGraph cert).adj_comm, test_final_z_y]
      simp
    simp [hyz]

private def abProjection
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → Fin (k - 1)
  | .inl (.core (.a p)) => p
  | .inl (.core (.b p)) => p
  | _ => Vertex.c0 cert

@[simp]
private theorem abProjection_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    abProjection cert (Vertex.a p) = p :=
  rfl

@[simp]
private theorem abProjection_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    abProjection cert (Vertex.b p) = p :=
  rfl

private theorem not_final_adj_a_b_same
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    ¬(finalGraph cert).Adj (Vertex.a p) (Vertex.b p) := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, Vertex.b]

/-- Row (R3): the switched edge `b₀y_*` has no red
`(k-1)`-clique in its common final-red neighborhood. -/
theorem red_safe_b0_ystar
    (cert : Certificates.OrderedCertificates G k s) :
    (finalGraph cert).CliqueFreeOn
      ((finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.y cert none))
      (k - 1) := by
  classical
  intro t htcommon ht
  have hinj : Set.InjOn (abProjection cert) t := by
    intro u hu v hv huv
    rcases (mem_common_b0_ystar_iff cert u).1 (htcommon hu) with
        ⟨p, hp0, rfl⟩ | hu1 | hu2
    · rcases (mem_common_b0_ystar_iff cert v).1 (htcommon hv) with
          ⟨q, hq0, rfl⟩ | hv1 | hv2
      · have hpq : p = q := by simpa using huv
        subst q
        rfl
      · subst v
        have hp : p = c1 cert := by simpa using huv
        subst p
        exact False.elim <| not_final_adj_a_b_same cert (c1 cert)
          (ht.isClique hu hv (by simp))
      · subst v
        have hp : p = Vertex.c2 cert := by simpa using huv
        subst p
        exact False.elim <| not_final_adj_a_b_same cert (Vertex.c2 cert)
          (ht.isClique hu hv (by simp))
    · subst u
      rcases (mem_common_b0_ystar_iff cert v).1 (htcommon hv) with
          ⟨q, hq0, rfl⟩ | hv1 | hv2
      · have hq : q = c1 cert := by simpa using huv.symm
        subst q
        exact False.elim <| not_final_adj_a_b_same cert (c1 cert)
          ((ht.isClique hu hv (by simp)).symm)
      · simpa [hv1]
      · subst v
        have hne : c1 cert ≠ Vertex.c2 cert := by
          intro h
          have hval := congrArg Fin.val h
          simp [c1, Vertex.c2, Certificates.c1Index] at hval
        exact False.elim (hne huv)
    · subst u
      rcases (mem_common_b0_ystar_iff cert v).1 (htcommon hv) with
          ⟨q, hq0, rfl⟩ | hv1 | hv2
      · have hq : q = Vertex.c2 cert := by simpa using huv.symm
        subst q
        exact False.elim <| not_final_adj_a_b_same cert (Vertex.c2 cert)
          ((ht.isClique hu hv (by simp)).symm)
      · subst v
        have hne : Vertex.c2 cert ≠ c1 cert := by
          intro h
          have hval := congrArg Fin.val h
          simp [c1, Vertex.c2, Certificates.c1Index] at hval
        exact False.elim (hne huv)
      · simpa [hv2]
  let image := t.image (abProjection cert)
  have himage :
      image ⊆ (Finset.univ.erase (Vertex.c0 cert)) := by
    intro p hp
    obtain ⟨w, hwt, rfl⟩ := Finset.mem_image.mp hp
    have hw := (mem_common_b0_ystar_iff cert w).1 (htcommon hwt)
    rcases hw with ⟨q, hq0, rfl⟩ | h1 | h2
    · simp [hq0]
    · subst w
      rw [Finset.mem_erase]
      exact ⟨(Certificates.c0_ne_c1 cert.five_le_k).symm,
        Finset.mem_univ _⟩
    · subst w
      have h02 : Vertex.c2 cert ≠ Vertex.c0 cert := by
        intro h
        have hv := congrArg Fin.val h
        simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
      simp [h02]
  have hcardImage : image.card = k - 1 := by
    rw [Finset.card_image_of_injOn hinj, ht.card_eq]
  have hcardErase :
      (Finset.univ.erase (Vertex.c0 cert) :
        Finset (Fin (k - 1))).card = k - 2 := by
    simp
    have hk := cert.five_le_k
    omega
  have hle := Finset.card_le_card himage
  rw [hcardImage, hcardErase] at hle
  have hk := cert.five_le_k
  omega

private theorem pre_b2_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (preGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.core v) ↔
      v ≠ cert.c (Vertex.c2 cert) ∧
        G.Adj (cert.c (Vertex.c2 cert)) v := by
  simp only [preGraph, Vertex.b, Vertex.core, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa using
    (specialLift_adj_b_core G cert.c (Vertex.c2 cert) v)

private theorem final_b2_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (finalGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.core v) ↔
      v ≠ cert.c (Vertex.c2 cert) ∧
        G.Adj (cert.c (Vertex.c2 cert)) v := by
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, pre_b2_core]

private theorem pre_b2_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (preGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.a p) ↔
      p ≠ Vertex.c2 cert := by
  simp only [preGraph, Vertex.b, Vertex.a, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa [ne_comm] using
    (specialLift_adj_b_a G cert.c (Vertex.c2 cert) p)

private theorem final_b2_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.a p) ↔
      p ≠ Vertex.c2 cert := by
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, pre_b2_a]

private theorem pre_b2_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (preGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.b p) ↔
      Vertex.c2 cert ≠ p ∧ SameBPart (Vertex.c2 cert) p := by
  simp only [preGraph, Vertex.b, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_core]
  simpa using
    (specialLift_adj_b_b G cert.c (Vertex.c2 cert) p)

private theorem final_b2_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj (Vertex.b (Vertex.c2 cert)) (Vertex.b p) ↔
      p = Vertex.c0 cert ∨
        (Vertex.c2 cert ≠ p ∧ SameBPart (Vertex.c2 cert) p) := by
  have h20 : Vertex.c2 cert ≠ Vertex.c0 cert := by
    intro h
    have hv := congrArg Fin.val h
    simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
  simp [finalGraph, removedRedGraph, removedRedRel, addedRedGraph,
    addedRedRel, pre_b2_b, h20]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.2
  · rintro (rfl | h)
    · exact Or.inr ⟨h20, rfl⟩
    · exact Or.inl h

private theorem pre_b2_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c2 cert)) (Vertex.x cert r) := by
  simp only [preGraph, Vertex.b, Vertex.x, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_a]
  change
    Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
        ((Canonical.outerIndexEquiv (hs cert)).symm r) ≠
      SpecialLiftVertex.b (Vertex.c2 cert)
  rw [secondCertificate_symm]
  cases r <;> simp [Canonical.secondCertificateAt]

private theorem final_b2_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.b (Vertex.c2 cert)) (Vertex.x cert r) := by
  have h20 : Vertex.c2 cert ≠ Vertex.c0 cert := by
    intro h
    have hv := congrArg Fin.val h
    simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
  rw [final_adj_iff]
  exact Or.inl ⟨pre_b2_x cert r, by
    simp [removedRedGraph, removedRedRel, h20]⟩

private theorem mem_common_b0_b2_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w : Vertex V k s) :
    w ∈ (finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.b (Vertex.c2 cert)) ↔
      (∃ v, G.Adj (cert.c (Vertex.c0 cert)) v ∧
          G.Adj (cert.c (Vertex.c2 cert)) v ∧
          w = Vertex.core v) ∨
      (∃ p, p ≠ Vertex.c0 cert ∧ p ≠ Vertex.c2 cert ∧
          w = Vertex.a p) ∨
      (∃ r, r ≠ some (Vertex.i1 cert) ∧ r ≠ none ∧
          w = Vertex.x cert r) ∨
      w = Vertex.y cert none := by
  rw [SimpleGraph.mem_commonNeighbors]
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    rw [test_final_b0_core, final_b2_core]
    constructor
    · rintro ⟨⟨_, h0⟩, _, h2⟩
      exact Or.inl ⟨v, h0, h2, rfl⟩
    · rintro (⟨_, h0, h2, h⟩ | h | h | h)
      · simp at h
        subst h
        exact ⟨⟨h0.ne.symm, h0⟩, h2.ne.symm, h2⟩
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · simp at h
  · obtain ⟨p, rfl⟩ := h
    rw [test_final_b0_a, final_b2_a]
    aesop
  · obtain ⟨p, rfl⟩ := h
    rw [test_final_b0_b, final_b2_b]
    have h02 : Vertex.c0 cert ≠ Vertex.c2 cert := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
    have hpart02 :
        ¬SameBPart (Vertex.c0 cert) (Vertex.c2 cert) := by
      simp [SameBPart, Vertex.c0, Vertex.c2, Certificates.c0Index]
    have hpart20 :
        ¬SameBPart (Vertex.c2 cert) (Vertex.c0 cert) := by
      rwa [sameBPart_comm]
    constructor
    · rintro ⟨h0 | h0, h2 | h2⟩
      · exact False.elim (h02 (h2.symm.trans h0))
      · subst p
        exact False.elim (h2.1 rfl)
      · subst p
        exact False.elim (h0.1 rfl)
      · rcases h0.2 with hsmall | hlarge
        · rcases h2.2 with hsmall' | hlarge'
          · simp [Vertex.c2] at hsmall'
          · omega
        · simp [Vertex.c0, Certificates.c0Index] at hlarge
    · intro h
      rcases h with h | h | h | h
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · simp at h
  · obtain ⟨r, rfl⟩ := h
    rw [test_final_b0_x]
    simp only [final_b2_x, and_true]
    aesop
  · obtain ⟨r, rfl⟩ := h
    rw [test_final_b0_y]
    cases r with
    | none =>
        have h2y :
            (finalGraph cert).Adj
              (Vertex.b (Vertex.c2 cert)) (Vertex.y cert none) :=
          (final_ystar_b cert (Vertex.c2 cert)).symm
        simp [h2y]
    | some q => simp
  · subst w
    have h20 : Vertex.c2 cert ≠ Vertex.c0 cert := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
    have hpart :
        ¬SameBPart (Vertex.c0 cert) (Vertex.c2 cert) := by
      simp [SameBPart, Vertex.c0, Vertex.c2, Certificates.c0Index]
    have hb2z :
        ¬(finalGraph cert).Adj (Vertex.b (Vertex.c2 cert)) Vertex.z := by
      rw [(finalGraph cert).adj_comm, test_final_z_b]
      simp [h20, hpart]
    simp [hb2z]

private def coreProjection
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → V
  | .inl (.core (.core v)) => v
  | _ => cert.c (Vertex.c0 cert)

@[simp]
private theorem coreProjection_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    coreProjection cert (Vertex.core v) = v :=
  rfl

private theorem final_core_core_iff
    (cert : Certificates.OrderedCertificates G k s) (v w : V) :
    (finalGraph cert).Adj (Vertex.core v) (Vertex.core w) ↔
      G.Adj v w := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.core]
  constructor
  · intro h
    exact h.2 h.1
  · intro h
    exact ⟨h.ne, fun _ ↦ h⟩

private theorem final_a_core_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) (v : V) :
    (finalGraph cert).Adj (Vertex.a p) (Vertex.core v) ↔
      cert.c p = v := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, Vertex.core]

private theorem not_final_adj_x_x
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    ¬(finalGraph cert).Adj (Vertex.x cert r) (Vertex.x cert t) := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.x]

/-- Row (R4): the switched edge `b₀b₂` has no red
`(k-1)`-clique in its common final-red neighborhood. -/
theorem red_safe_b0_b2
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    (finalGraph cert).CliqueFreeOn
      ((finalGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.b (Vertex.c2 cert)))
      (k - 1) := by
  classical
  intro t htcommon ht
  let td := t.filter fun w ↦ ∃ v, w = Vertex.core v
  let ta := t.filter fun w ↦ ∃ p, w = Vertex.a p
  let tx := t.filter fun w ↦ ∃ r, w = Vertex.x cert r
  let ty := t.filter fun w ↦ w = Vertex.y cert none
  have hcover : (((td ∪ ta) ∪ tx) ∪ ty) = t := by
    ext w
    constructor
    · simp only [Finset.mem_union, Finset.mem_filter, td, ta, tx, ty]
      tauto
    · intro hw
      have hc := (mem_common_b0_b2_iff cert w).1 (htcommon hw)
      simp only [Finset.mem_union, Finset.mem_filter, td, ta, tx, ty]
      rcases hc with hc | ha | hx | hy
      · obtain ⟨v, _, _, rfl⟩ := hc
        exact Or.inl (Or.inl (Or.inl ⟨hw, v, rfl⟩))
      · obtain ⟨p, _, _, rfl⟩ := ha
        exact Or.inl (Or.inl (Or.inr ⟨hw, p, rfl⟩))
      · obtain ⟨r, _, _, rfl⟩ := hx
        exact Or.inl (Or.inr ⟨hw, r, rfl⟩)
      · subst w
        exact Or.inr ⟨hw, rfl⟩
  have hda : Disjoint td ta := by
    rw [Finset.disjoint_left]
    intro w hwd hwa
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwd
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwa
    rw [hv] at hp
    simp at hp
  have hdx : Disjoint td tx := by
    rw [Finset.disjoint_left]
    intro w hwd hwx
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwd
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    rw [hv] at hr
    simp at hr
  have hdy : Disjoint td ty := by
    rw [Finset.disjoint_left]
    intro w hwd hwy
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwd
    have hy := (Finset.mem_filter.mp hwy).2
    rw [hv] at hy
    simp at hy
  have hax : Disjoint ta tx := by
    rw [Finset.disjoint_left]
    intro w hwa hwx
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwa
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    rw [hp] at hr
    simp at hr
  have hay : Disjoint ta ty := by
    rw [Finset.disjoint_left]
    intro w hwa hwy
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwa
    have hy := (Finset.mem_filter.mp hwy).2
    rw [hp] at hy
    simp at hy
  have hxy : Disjoint tx ty := by
    rw [Finset.disjoint_left]
    intro w hwx hwy
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    have hy := (Finset.mem_filter.mp hwy).2
    rw [hr] at hy
    simp at hy
  have hdax : Disjoint (td ∪ ta) tx :=
    Finset.disjoint_union_left.2 ⟨hdx, hax⟩
  have hdaxy : Disjoint ((td ∪ ta) ∪ tx) ty :=
    Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_left.2 ⟨hdy, hay⟩, hxy⟩
  have hcard :
      td.card + ta.card + tx.card + ty.card = k - 1 := by
    calc
      td.card + ta.card + tx.card + ty.card =
          (((td ∪ ta) ∪ tx) ∪ ty).card := by
            symm
            rw [Finset.card_union_of_disjoint hdaxy,
              Finset.card_union_of_disjoint hdax,
              Finset.card_union_of_disjoint hda]
      _ = t.card := by rw [hcover]
      _ = k - 1 := ht.card_eq
  have haBound : ta.card ≤ k - 3 := by
    have hainj : Set.InjOn (abProjection cert) ta := by
      intro u hu v hv huv
      obtain ⟨p, rfl⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨q, rfl⟩ := (Finset.mem_filter.mp hv).2
      have hpq : p = q := by simpa using huv
      subst q
      rfl
    let ai := ta.image (abProjection cert)
    have haisub :
        ai ⊆
          ((Finset.univ.erase (Vertex.c0 cert)).erase
            (Vertex.c2 cert)) := by
      intro p hp
      obtain ⟨w, hwta, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q, rfl⟩ := (Finset.mem_filter.mp hwta).2
      have hwcommon := htcommon (Finset.mem_filter.mp hwta).1
      rcases (mem_common_b0_b2_iff cert (Vertex.a q)).1 hwcommon with
          hc | ha | hx | hy
      · obtain ⟨_, _, _, hfalse⟩ := hc
        simp at hfalse
      · obtain ⟨p, hp0, hp2, hp⟩ := ha
        have hpq : p = q := by simpa using hp.symm
        subst p
        simp [hp0, hp2]
      · obtain ⟨_, _, _, hfalse⟩ := hx
        simp at hfalse
      · simp at hy
    have haiCard : ai.card = ta.card := by
      rw [Finset.card_image_of_injOn hainj]
    have heraseCard :
        ((Finset.univ.erase (Vertex.c0 cert)).erase
          (Vertex.c2 cert) : Finset (Fin (k - 1))).card = k - 3 := by
      have h20 : Vertex.c2 cert ≠ Vertex.c0 cert := by
        intro h
        have hv := congrArg Fin.val h
        simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
      simp [h20]
      have hk := cert.five_le_k
      omega
    have hle := Finset.card_le_card haisub
    rw [haiCard, heraseCard] at hle
    exact hle
  have hxBound : tx.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨q, rfl⟩ := (Finset.mem_filter.mp hv).2
    by_contra hne
    exact not_final_adj_x_x cert r q
      (ht.isClique (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hv).1 hne)
  have hyBound : ty.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
  have hdBound : td.card ≤ k - 3 := by
    have hdinj : Set.InjOn (coreProjection cert) td := by
      intro u hu v hv huv
      obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hv).2
      have hxy : x = y := by simpa using huv
      subst y
      rfl
    let di := td.image (coreProjection cert)
    have hdiCard : di.card = td.card := by
      rw [Finset.card_image_of_injOn hdinj]
    have hdiClique : G.IsClique (di : Set V) := by
      intro x hx y hy hxy
      obtain ⟨u, hutd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hvtd, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hutd).2
      obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hvtd).2
      rw [← final_core_core_iff cert]
      exact ht.isClique
        (Finset.mem_filter.mp hutd).1
        (Finset.mem_filter.mp hvtd).1
        (by
          intro h
          apply hxy
          simpa using h)
    have h0adj :
        ∀ x ∈ di, G.Adj (cert.c (Vertex.c0 cert)) x := by
      intro x hx
      obtain ⟨u, hutd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hutd).2
      have hc := (mem_common_b0_b2_iff cert (Vertex.core x)).1
        (htcommon (Finset.mem_filter.mp hutd).1)
      rcases hc with hc | ha | hx | hy
      · obtain ⟨v, h0, _, hv⟩ := hc
        have hxv : x = v := by simpa using hv
        subst v
        simpa using h0
      · obtain ⟨_, _, _, hfalse⟩ := ha
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := hx
        simp at hfalse
      · simp at hy
    have h2adj :
        ∀ x ∈ di, G.Adj (cert.c (Vertex.c2 cert)) x := by
      intro x hx
      obtain ⟨u, hutd, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hutd).2
      have hc := (mem_common_b0_b2_iff cert (Vertex.core x)).1
        (htcommon (Finset.mem_filter.mp hutd).1)
      rcases hc with hc | ha | hx | hy
      · obtain ⟨v, _, h2, hv⟩ := hc
        have hxv : x = v := by simpa using hv
        subst v
        simpa using h2
      · obtain ⟨_, _, _, hfalse⟩ := ha
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := hx
        simp at hfalse
      · simp at hy
    have h0not : cert.c (Vertex.c0 cert) ∉ di := by
      intro h
      exact G.loopless.irrefl _ (h0adj _ h)
    have h2not : cert.c (Vertex.c2 cert) ∉ di := by
      intro h
      exact G.loopless.irrefl _ (h2adj _ h)
    have h02 :
        cert.c (Vertex.c0 cert) ≠ cert.c (Vertex.c2 cert) := by
      apply cert.c.injective.ne
      intro h
      have hv := congrArg Fin.val h
      simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv
    let big :=
      insert (cert.c (Vertex.c0 cert))
        (insert (cert.c (Vertex.c2 cert)) di)
    have hbigClique : G.IsClique (big : Set V) := by
      have hinner :
          G.IsClique
            (↑(insert (cert.c (Vertex.c2 cert)) di) : Set V) := by
        rw [Finset.coe_insert]
        exact hdiClique.insert fun x hx _ ↦ h2adj x hx
      rw [Finset.coe_insert]
      exact hinner.insert fun x hx _ ↦ by
        simp only [Finset.coe_insert, Set.mem_insert_iff,
          Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact cert.c_adj (by
            intro h
            have hv := congrArg Fin.val h
            simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hv)
        · exact h0adj x hx
    have h0notInner :
        cert.c (Vertex.c0 cert) ∉
          insert (cert.c (Vertex.c2 cert)) di := by
      simp [h02, h0not]
    have hbigCard : big.card = td.card + 2 := by
      dsimp [big]
      rw [Finset.card_insert_of_notMem h0notInner,
        Finset.card_insert_of_notMem h2not, hdiCard]
    have hlt : big.card < k := by
      let f : {x // x ∈ big} ↪ V :=
        ⟨Subtype.val, Subtype.val_injective⟩
      have hf :=
        card_lt_of_cliqueFree_of_embedding hG.1 f (fun x y hxy ↦
          hbigClique x.property y.property
            (fun h ↦ hxy (Subtype.ext h)))
      simpa using hf
    rw [hbigCard] at hlt
    have hk := cert.five_le_k
    omega
  by_cases hy0 : ty.card = 0
  · by_cases ha0 : ta.card = 0
    · have hk := cert.five_le_k
      omega
    · have hapos : 0 < ta.card := Nat.pos_of_ne_zero ha0
      obtain ⟨aw, hawta⟩ := Finset.card_pos.mp hapos
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hawta).2
      subst aw
      have hawt : Vertex.a p ∈ t := (Finset.mem_filter.mp hawta).1
      have hdOne : td.card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro u v hu hv
        obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hu).2
        obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hv).2
        have hpx :
            cert.c p = x :=
          (final_a_core_iff cert p x).1
            (ht.isClique hawt (Finset.mem_filter.mp hu).1 (by simp))
        have hpy :
            cert.c p = y :=
          (final_a_core_iff cert p y).1
            (ht.isClique hawt (Finset.mem_filter.mp hv).1 (by simp))
        simp [hpx.symm.trans hpy]
      by_cases haTwo : 2 ≤ ta.card
      · obtain ⟨au, hauta, av, havta, huv⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < ta.card)
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hauta).2
        obtain ⟨q, hq⟩ := (Finset.mem_filter.mp havta).2
        subst au
        subst av
        have hpq : p ≠ q := by
          intro h
          subst q
          exact huv rfl
        have haut : Vertex.a p ∈ t := (Finset.mem_filter.mp hauta).1
        have havt : Vertex.a q ∈ t := (Finset.mem_filter.mp havta).1
        have hd0 : td.card = 0 := by
          rw [Finset.card_eq_zero]
          apply Finset.eq_empty_iff_forall_notMem.2
          intro w hw
          obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hw).2
          have hpx :
              cert.c p = x :=
            (final_a_core_iff cert p x).1
              (ht.isClique haut (Finset.mem_filter.mp hw).1 (by simp))
          have hqx :
              cert.c q = x :=
            (final_a_core_iff cert q x).1
              (ht.isClique havt (Finset.mem_filter.mp hw).1 (by simp))
          exact hpq (cert.c.injective (hpx.trans hqx.symm))
        have hk := cert.five_le_k
        omega
      · have haOne : ta.card ≤ 1 := by omega
        have hk := cert.five_le_k
        omega
  · have hypos : 0 < ty.card := Nat.pos_of_ne_zero hy0
    obtain ⟨yw, hywty⟩ := Finset.card_pos.mp hypos
    have hyweq := (Finset.mem_filter.mp hywty).2
    subst yw
    have hywt : Vertex.y cert none ∈ t :=
      (Finset.mem_filter.mp hywty).1
    have hd0 : td.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.2
      intro w hw
      obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hw).2
      have hyx :=
        (final_ystar_core cert x).1
          (ht.isClique hywt (Finset.mem_filter.mp hw).1 (by simp))
      have hc := (mem_common_b0_b2_iff cert (Vertex.core x)).1
        (htcommon (Finset.mem_filter.mp hw).1)
      rcases hc with hc | ha | hx | hy
      · obtain ⟨v, h0, _, hv⟩ := hc
        have hxv : x = v := by simpa using hv
        subst v
        rw [hyx] at h0
        exact G.loopless.irrefl _ h0
      · obtain ⟨_, _, _, hfalse⟩ := ha
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := hx
        simp at hfalse
      · simp at hy
    have hx0 : tx.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.2
      intro w hw
      obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hw).2
      have hyr :=
        (final_ystar_x cert r).1
          (ht.isClique hywt (Finset.mem_filter.mp hw).1 (by simp))
      have hc := (mem_common_b0_b2_iff cert (Vertex.x cert r)).1
        (htcommon (Finset.mem_filter.mp hw).1)
      rcases hc with hc | ha | hx | hy
      · obtain ⟨_, _, _, hfalse⟩ := hc
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := ha
        simp at hfalse
      · obtain ⟨q, _, hqnone, hEq⟩ := hx
        have hrq : r = q := by simpa using hEq
        subst q
        exact hqnone hyr
      · simp at hy
    have hk := cert.five_le_k
    omega

private theorem pre_y_first
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (d : SpecialLiftVertex V k) :
    (preGraph cert).Adj (Vertex.y cert (some q)) (.inl (.core d)) ↔
      d = .core (cert.i q) ∨
        (specialLift G cert.c).Adj (.core (cert.i q)) d := by
  simp only [preGraph, Vertex.y, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_b_core]
  simp only [compl_compl]
  change
    d =
          Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm (some q)) ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm (some q))) d ↔
      d = .core (cert.i q) ∨
        (specialLift G cert.c).Adj (.core (cert.i q)) d
  rw [secondCertificate_symm]
  rfl

private theorem final_a0_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.core v) ↔
      v = cert.c (Vertex.c0 cert) := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, Vertex.core]
  exact eq_comm

private theorem final_a0_b
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.b p) ↔
      p ≠ Vertex.c0 cert := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, Vertex.b, ne_comm]

private theorem final_a0_a
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.a p) ↔
      p ≠ Vertex.c0 cert := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, ne_comm]

private theorem final_y_core
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (v : V) :
    (finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.core v) ↔
      v = cert.i q ∨ G.Adj (cert.i q) v := by
  rw [final_adj_iff]
  simp [pre_y_first, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel]

private theorem final_y_b_of_ne_c0
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1))
    (hp0 : p ≠ Vertex.c0 cert) :
    (finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.b p) ↔
      G.Adj (cert.c p) (cert.i q) := by
  rw [final_adj_iff]
  simp [pre_y_first, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hp0, cert.c_ne_i p q,
    (cert.c_ne_i p q).symm]

private theorem pre_a0_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert r) ↔
      r ≠ none := by
  simp only [preGraph, Vertex.a, Vertex.x, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_a]
  change
    Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
        ((Canonical.outerIndexEquiv (hs cert)).symm r) ≠
        SpecialLiftVertex.a (Vertex.c0 cert) ↔ r ≠ none
  rw [secondCertificate_symm]
  cases r with
  | none => simp [Canonical.secondCertificateAt]
  | some q => simp [Canonical.secondCertificateAt]

private theorem final_a0_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert r) ↔
      ∃ q, q ∉ cert.E ∧ r = some q := by
  cases r with
  | none =>
      rw [final_adj_iff]
      simp [pre_a0_x, removedRedGraph, removedRedRel,
        addedRedGraph, addedRedRel]
  | some q =>
      have hrem :
          (removedRedGraph cert).Adj
              (Vertex.a (Vertex.c0 cert))
              (Vertex.x cert (some q)) ↔
            q ∈ cert.E := by
        simp [removedRedGraph, removedRedRel]
      have hadd :
          ¬(addedRedGraph cert).Adj
              (Vertex.a (Vertex.c0 cert))
              (Vertex.x cert (some q)) := by
        simp [addedRedGraph, addedRedRel]
      rw [final_adj_iff, hrem]
      simp [pre_a0_x, hadd]

private theorem final_y_x
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.x cert r) ↔
      r = some q := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.y, Vertex.x]

private theorem final_y_x_general
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.y cert r) (Vertex.x cert t) ↔ t = r := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.y, Vertex.x]

private theorem final_b_b_of_ne_c0
    (cert : Certificates.OrderedCertificates G k s)
    (p r : Fin (k - 1))
    (hp0 : p ≠ Vertex.c0 cert) (hr0 : r ≠ Vertex.c0 cert) :
    (finalGraph cert).Adj (Vertex.b p) (Vertex.b r) ↔
      p ≠ r ∧ SameBPart p r := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.b, hp0, hr0]
  intro hne
  constructor
  · intro h
    exact (h hne).2
  · intro h
    exact fun _ ↦ ⟨hne, h⟩

private theorem pre_a0_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert r) ↔
      r = none := by
  simp only [preGraph, Vertex.a, Vertex.y, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  rw [specialLift_compl_adj_core_b]
  simp only [compl_compl]
  change
    SpecialLiftVertex.a (Vertex.c0 cert) =
          Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm r) ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificate cert.toCertificates cert.five_le_k (hs cert)
            ((Canonical.outerIndexEquiv (hs cert)).symm r))
          (.a (Vertex.c0 cert)) ↔ r = none
  rw [secondCertificate_symm]
  cases r with
  | none => simp [Canonical.secondCertificateAt]
  | some q =>
      simp [Canonical.secondCertificateAt, cert.c_ne_i (Vertex.c0 cert) q]

private theorem final_a0_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert r) ↔
      r = none ∨ ∃ q ∈ cert.T, r = some q := by
  rw [final_adj_iff]
  simp [pre_a0_y, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel]

private theorem not_final_y_a_of_ne
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1))
    (hp0 : p ≠ Vertex.c0 cert) :
    ¬(finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.a p) := by
  rw [final_adj_iff]
  simp [pre_y_first, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, cert.c_ne_i p q, hp0]

private theorem not_final_a0_z
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(finalGraph cert).Adj (Vertex.a (Vertex.c0 cert)) Vertex.z := by
  rw [final_adj_iff]
  simp [preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.a, Vertex.b]

private theorem mem_common_a0_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)} (hqT : q ∈ cert.T)
    (w : Vertex V k s) :
    w ∈ (finalGraph cert).commonNeighbors
        (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
      w = Vertex.core (cert.c (Vertex.c0 cert)) ∨
      (∃ p, p ≠ Vertex.c0 cert ∧
          G.Adj (cert.c p) (cert.i q) ∧ w = Vertex.b p) ∨
      (q ∉ cert.E ∧ w = Vertex.x cert (some q)) ∨
      (∃ r, (finalGraph cert).Adj
          (Vertex.a (Vertex.c0 cert)) (Vertex.y cert r) ∧
        (finalGraph cert).Adj
          (Vertex.y cert (some q)) (Vertex.y cert r) ∧
        w = Vertex.y cert r) := by
  rw [SimpleGraph.mem_commonNeighbors]
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    rw [final_a0_core]
    constructor
    · rintro ⟨hv, hy⟩
      subst v
      exact Or.inl rfl
    · rintro (h | h | h | h)
      · simp at h
        subst v
        constructor
        · rfl
        · exact (final_y_core cert q
            (cert.c (Vertex.c0 cert))).2
              (Or.inr ((cert.mem_T q).1 hqT).symm)
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · simp at h
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
  · obtain ⟨p, rfl⟩ := h
    rw [final_a0_a]
    constructor
    · rintro ⟨hp0, hy⟩
      exact False.elim (not_final_y_a_of_ne cert q p hp0 hy)
    · intro h
      rcases h with h | h | h | h
      · simp at h
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · simp at h
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
  · obtain ⟨p, rfl⟩ := h
    rw [final_a0_b]
    constructor
    · rintro ⟨hp0, hy⟩
      exact Or.inr (Or.inl
        ⟨p, hp0, (final_y_b_of_ne_c0 cert q p hp0).1 hy, rfl⟩)
    · rintro (h | h | h | h)
      · simp at h
      · obtain ⟨r, hr0, hr, hEq⟩ := h
        have hrp : r = p := by simpa using hEq.symm
        subst r
        exact ⟨hr0, (final_y_b_of_ne_c0 cert q p hr0).2 hr⟩
      · obtain ⟨_, hfalse⟩ := h
        simp at hfalse
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
  · obtain ⟨r, rfl⟩ := h
    rw [final_a0_x, final_y_x]
    constructor
    · rintro ⟨⟨t, htE, hrt⟩, hrq⟩
      have htq : t = q := by simpa [hrq] using hrt.symm
      subst t
      exact Or.inr (Or.inr (Or.inl ⟨htE, by simpa [hrq]⟩))
    · rintro (h | h | h | h)
      · simp at h
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
      · obtain ⟨hqE, hEq⟩ := h
        have hrq : r = some q := by simpa using hEq
        exact ⟨⟨q, hqE, hrq⟩, hrq⟩
      · obtain ⟨_, _, _, hfalse⟩ := h
        simp at hfalse
  · obtain ⟨r, rfl⟩ := h
    aesop
  · subst w
    simp [not_final_a0_z cert]

private abbrev yIndex
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) : Fin s :=
  (Canonical.outerIndexEquiv (hs cert)).symm r

@[simp]
private theorem yIndex_some_val
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (yIndex cert (some q)).val = q.val := by
  simp [yIndex, Canonical.outerIndexEquiv]

@[simp]
private theorem yIndex_none_val
    (cert : Certificates.OrderedCertificates G k s) :
    (yIndex cert none).val = s - 1 := by
  simp [yIndex, Canonical.outerIndexEquiv]

private theorem pre_y_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (preGraph cert).Adj (Vertex.y cert r) (Vertex.y cert t) ↔
      yIndex (s := s) cert r ≠ yIndex (s := s) cert t ∧
        ¬SameBPart (k := s + 1)
          (yIndex (s := s) cert r) (yIndex (s := s) cert t) := by
  simp only [preGraph, Vertex.y, redJoinedClone.adj_old_old,
    canonicalGraph, Canonical.graph]
  exact specialLift_compl_adj_b_b _ _ _ _

private theorem final_y_y_to_pre
    (cert : Certificates.OrderedCertificates G k s)
    {r t : Option (Fin (s - 1))}
    (h : (finalGraph cert).Adj
      (Vertex.y cert r) (Vertex.y cert t)) :
    (preGraph cert).Adj (Vertex.y cert r) (Vertex.y cert t) := by
  rcases (final_adj_iff cert _ _).1 h with hpre | hadd
  · exact hpre.1
  · simp [addedRedGraph, addedRedRel] at hadd

private theorem sameBPart_of_not_sameBPart_both
    {n : ℕ} {p q r : Fin n}
    (hpq : ¬SameBPart (k := n + 1) p q)
    (hpr : ¬SameBPart (k := n + 1) p r) :
    SameBPart (k := n + 1) q r := by
  simp only [SameBPart] at hpq hpr ⊢
  by_cases hp : p.val < 2
  · right
    constructor <;> omega
  · left
    constructor <;> omega

private theorem not_final_y_triangle
    (cert : Certificates.OrderedCertificates G k s)
    (r t u : Option (Fin (s - 1)))
    (hrt : (finalGraph cert).Adj
      (Vertex.y cert r) (Vertex.y cert t))
    (hru : (finalGraph cert).Adj
      (Vertex.y cert r) (Vertex.y cert u)) :
    ¬(finalGraph cert).Adj
      (Vertex.y cert t) (Vertex.y cert u) := by
  intro htu
  have hrt' := (pre_y_y_iff cert r t).1
    (final_y_y_to_pre cert hrt)
  have hru' := (pre_y_y_iff cert r u).1
    (final_y_y_to_pre cert hru)
  have htu' := (pre_y_y_iff cert t u).1
    (final_y_y_to_pre cert htu)
  exact htu'.2
    (sameBPart_of_not_sameBPart_both hrt'.2 hru'.2)

private theorem not_final_y_y_of_samePart
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1)))
    (hpart : SameBPart (k := s + 1)
      (yIndex (s := s) cert r) (yIndex (s := s) cert t)) :
    ¬(finalGraph cert).Adj (Vertex.y cert r) (Vertex.y cert t) := by
  intro h
  exact ((pre_y_y_iff cert r t).1
    (final_y_y_to_pre cert h)).2 hpart

private theorem not_final_y_y_of_removed
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1)))
    (hrem : (removedRedGraph cert).Adj
      (Vertex.y cert r) (Vertex.y cert t)) :
    ¬(finalGraph cert).Adj (Vertex.y cert r) (Vertex.y cert t) := by
  intro h
  rcases (final_adj_iff cert _ _).1 h with hpre | hadd
  · exact hpre.2 hrem
  · simp [addedRedGraph, addedRedRel] at hadd

private theorem eq_i1_or_two_le_of_mem_E
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) :
    q = Vertex.i1 cert ∨ 2 ≤ q.val := by
  obtain ⟨hB⟩ :=
    (cert.E_nonempty_iff_caseB hG).1 ⟨q, hqE⟩
  have hqT := cert.E_subset_T hqE
  have h0U := cert.caseB_i0_mem_U hB
  by_cases hq1 : q.val = 1
  · left
    apply Fin.ext
    simpa [Vertex.i1, Certificates.i1Index'] using hq1
  · right
    have hq0 : q.val ≠ 0 := by
      intro hval
      have hqi0 : q =
          Certificates.i0Index' cert.five_le_s := by
        apply Fin.ext
        simpa using hval
      subst q
      exact ((cert.mem_U _).1 h0U) hqT
    omega

private theorem removed_y1_ystar
    (cert : Certificates.OrderedCertificates G k s)
    (hE : cert.E.Nonempty) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert none) := by
  simp [removedRedGraph, removedRedRel, hE]

private theorem removed_y1_y_large_E
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) (hq2 : 2 ≤ q.val) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert (some q)) := by
  simp [removedRedGraph, removedRedRel, hq2]
  refine ⟨?_, (cert.mem_T q).1 ((cert.mem_E q).1 hqE).1,
    ((cert.mem_E q).1 hqE).2⟩
  intro h
  have hv := congrArg Fin.val h
  simp [Vertex.i1, Certificates.i1Index'] at hv
  omega

private theorem not_final_y_E_ystar
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) :
    ¬(finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert none) := by
  rcases eq_i1_or_two_le_of_mem_E cert hG hqE with hq1 | hq2
  · subst q
    exact not_final_y_y_of_removed cert _ _
      (removed_y1_ystar cert ⟨_, hqE⟩)
  · apply not_final_y_y_of_samePart cert
    exact Or.inr ⟨by simpa using hq2, by
      have hs5 := cert.five_le_s
      simp
      omega⟩

private theorem not_final_y_E_E
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q t : Fin (s - 1)} (hqE : q ∈ cert.E) (htE : t ∈ cert.E) :
    ¬(finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert (some t)) := by
  rcases eq_i1_or_two_le_of_mem_E cert hG hqE with hq1 | hq2
  · subst q
    rcases eq_i1_or_two_le_of_mem_E cert hG htE with ht1 | ht2
    · subst t
      simp
    · exact not_final_y_y_of_removed cert _ _
        (removed_y1_y_large_E cert htE ht2)
  · rcases eq_i1_or_two_le_of_mem_E cert hG htE with ht1 | ht2
    · subst t
      rw [(finalGraph cert).adj_comm]
      exact not_final_y_y_of_removed cert _ _
        (removed_y1_y_large_E cert hqE hq2)
    · apply not_final_y_y_of_samePart cert
      exact Or.inr ⟨by simpa using hq2, by simpa using ht2⟩

private theorem y_common_mem_S_of_mem_E
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E)
    {r : Option (Fin (s - 1))}
    (ha : (finalGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert r))
    (hy : (finalGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert r)) :
    ∃ t ∈ cert.S, r = some t := by
  rcases (final_a0_y cert r).1 ha with rfl | ⟨t, htT, rfl⟩
  · exact False.elim (not_final_y_E_ystar cert hG hqE hy)
  · have htE : t ∉ cert.E := by
      intro htE
      exact not_final_y_E_E cert hG hqE htE hy
    exact ⟨t, (cert.mem_S t).2 ⟨htT, htE⟩, rfl⟩

/-- Row (R2): every switched edge `a₀y_q`, `q ∈ T`, has no red
`(k-1)`-clique in its common final-red neighborhood. -/
theorem red_safe_a0_y
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqT : q ∈ cert.T) :
    (finalGraph cert).CliqueFreeOn
      ((finalGraph cert).commonNeighbors
        (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)))
      (k - 1) := by
  classical
  intro t htcommon ht
  let tc := t.filter fun w ↦ ∃ v, w = Vertex.core v
  let tb := t.filter fun w ↦ ∃ p, w = Vertex.b p
  let tx := t.filter fun w ↦ ∃ r, w = Vertex.x cert r
  let ty := t.filter fun w ↦ ∃ r, w = Vertex.y cert r
  have hcover : (((tc ∪ tb) ∪ tx) ∪ ty) = t := by
    ext w
    constructor
    · simp only [Finset.mem_union, Finset.mem_filter, tc, tb, tx, ty]
      tauto
    · intro hw
      have hc := (mem_common_a0_y_iff cert hqT w).1 (htcommon hw)
      simp only [Finset.mem_union, Finset.mem_filter, tc, tb, tx, ty]
      rcases hc with hc | hb | hx | hy
      · exact Or.inl (Or.inl (Or.inl
          ⟨hw, cert.c (Vertex.c0 cert), hc⟩))
      · obtain ⟨p, _, _, rfl⟩ := hb
        exact Or.inl (Or.inl (Or.inr ⟨hw, p, rfl⟩))
      · obtain ⟨_, rfl⟩ := hx
        exact Or.inl (Or.inr ⟨hw, some q, rfl⟩)
      · obtain ⟨r, _, _, rfl⟩ := hy
        exact Or.inr ⟨hw, r, rfl⟩
  have hcb : Disjoint tc tb := by
    rw [Finset.disjoint_left]
    intro w hwc hwb
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwc
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwb
    rw [hv] at hp
    simp at hp
  have hcx : Disjoint tc tx := by
    rw [Finset.disjoint_left]
    intro w hwc hwx
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwc
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    rw [hv] at hr
    simp at hr
  have hcy : Disjoint tc ty := by
    rw [Finset.disjoint_left]
    intro w hwc hwy
    obtain ⟨_, v, hv⟩ := Finset.mem_filter.mp hwc
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwy
    rw [hv] at hr
    simp at hr
  have hbx : Disjoint tb tx := by
    rw [Finset.disjoint_left]
    intro w hwb hwx
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwb
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    rw [hp] at hr
    simp at hr
  have hby : Disjoint tb ty := by
    rw [Finset.disjoint_left]
    intro w hwb hwy
    obtain ⟨_, p, hp⟩ := Finset.mem_filter.mp hwb
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwy
    rw [hp] at hr
    simp at hr
  have hxy : Disjoint tx ty := by
    rw [Finset.disjoint_left]
    intro w hwx hwy
    obtain ⟨_, r, hr⟩ := Finset.mem_filter.mp hwx
    obtain ⟨_, u, hu⟩ := Finset.mem_filter.mp hwy
    rw [hr] at hu
    simp at hu
  have hcbx : Disjoint (tc ∪ tb) tx :=
    Finset.disjoint_union_left.2 ⟨hcx, hbx⟩
  have hcbxy : Disjoint ((tc ∪ tb) ∪ tx) ty :=
    Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_left.2 ⟨hcy, hby⟩, hxy⟩
  have hcard :
      tc.card + tb.card + tx.card + ty.card = k - 1 := by
    calc
      tc.card + tb.card + tx.card + ty.card =
          (((tc ∪ tb) ∪ tx) ∪ ty).card := by
            symm
            rw [Finset.card_union_of_disjoint hcbxy,
              Finset.card_union_of_disjoint hcbx,
              Finset.card_union_of_disjoint hcb]
      _ = t.card := by rw [hcover]
      _ = k - 1 := ht.card_eq
  have hcBound : tc.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    obtain ⟨x, rfl⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨y, rfl⟩ := (Finset.mem_filter.mp hv).2
    have hx := (final_a0_core cert x).1
      (((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hu).1)).1)
    have hy := (final_a0_core cert y).1
      (((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hv).1)).1)
    simp [hx.trans hy.symm]
  have hxBound : tx.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨z, rfl⟩ := (Finset.mem_filter.mp hv).2
    have hr := (final_y_x cert q r).1
      (((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hu).1)).2)
    have hz := (final_y_x cert q z).1
      (((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hv).1)).2)
    simp [hr.trans hz.symm]
  have hyBound : ty.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨z, rfl⟩ := (Finset.mem_filter.mp hv).2
    by_contra hrz
    have hqr :=
      ((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hu).1)).2
    have hqz :=
      ((finalGraph cert).mem_commonNeighbors.1
        (htcommon (Finset.mem_filter.mp hv).1)).2
    exact not_final_y_triangle cert (some q) r z hqr hqz
      (ht.isClique (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hv).1 hrz)
  have hxyBound : tx.card + ty.card ≤ 1 := by
    by_cases hx0 : tx.card = 0
    · omega
    · have hxpos : 0 < tx.card := Nat.pos_of_ne_zero hx0
      obtain ⟨xw, hxwtx⟩ := Finset.card_pos.mp hxpos
      obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hxwtx).2
      subst xw
      have hrq := (final_y_x cert q r).1
        (((finalGraph cert).mem_commonNeighbors.1
          (htcommon (Finset.mem_filter.mp hxwtx).1)).2)
      have hy0 : ty.card = 0 := by
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.2
        intro yw hyw
        obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hyw).2
        subst yw
        have hqz :=
          ((finalGraph cert).mem_commonNeighbors.1
            (htcommon (Finset.mem_filter.mp hyw).1)).2
        have hrz := (final_y_x_general cert z r).1
          ((finalGraph cert).adj_symm
            (ht.isClique (Finset.mem_filter.mp hxwtx).1
              (Finset.mem_filter.mp hyw).1 (by simp)))
        have hzq : z = some q := by
          rw [hrq] at hrz
          exact hrz.symm
        exact (finalGraph cert).loopless.irrefl
          (Vertex.y cert (some q)) (by simpa [hzq] using hqz)
      omega
  have hbdata :
      ∀ {p : Fin (k - 1)}, Vertex.b p ∈ tb →
        p ≠ Vertex.c0 cert ∧ G.Adj (cert.c p) (cert.i q) := by
    intro p hp
    have hc := (mem_common_a0_y_iff cert hqT (Vertex.b p)).1
      (htcommon (Finset.mem_filter.mp hp).1)
    rcases hc with hc | hb | hx | hy
    · simp at hc
    · obtain ⟨r, hr0, hrAdj, hr⟩ := hb
      have hrp : r = p := by simpa using hr.symm
      subst r
      exact ⟨hr0, hrAdj⟩
    · simp at hx
    · obtain ⟨_, _, _, hfalse⟩ := hy
      simp at hfalse
  have hbinj : Set.InjOn (abProjection cert) tb := by
    intro u hu v hv huv
    obtain ⟨p, rfl⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hv).2
    have hpr : p = r := by simpa using huv
    subst r
    rfl
  let bi := tb.image (abProjection cert)
  have hbiCard : bi.card = tb.card := by
    rw [Finset.card_image_of_injOn hbinj]
  have missingLarge_of_mem_S :
      ∀ {r : Fin (s - 1)}, r ∈ cert.S →
        ∃ m : Fin (k - 1),
          2 ≤ m.val ∧ ¬G.Adj (cert.c m) (cert.i r) := by
    intro r hrS
    have hrSdata := (cert.mem_S r).1 hrS
    have hnotall :
        ¬∀ m : Fin (k - 1), 2 ≤ m.val →
          G.Adj (cert.c m) (cert.i r) := by
      intro hall
      exact hrSdata.2 ((cert.mem_E r).2 ⟨hrSdata.1, hall⟩)
    push Not at hnotall
    exact hnotall
  have c0_ne_c1 :
      Vertex.c0 cert ≠ c1 cert :=
    Certificates.c0_ne_c1 cert.five_le_k
  by_cases hqE : q ∈ cert.E
  · have hx0 : tx.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.2
      intro w hw
      obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hw).2
      have hc := (mem_common_a0_y_iff cert hqT
        (Vertex.x cert r)).1
          (htcommon (Finset.mem_filter.mp hw).1)
      rcases hc with hc | hb | hx | hy
      · simp at hc
      · obtain ⟨_, _, _, hfalse⟩ := hb
        simp at hfalse
      · exact hx.1 hqE
      · obtain ⟨_, _, _, hfalse⟩ := hy
        simp at hfalse
    have hbE : tb.card ≤ k - 3 := by
      have hbeta := cert.beta_eq_c1_of_mem_E hG hqE
      have hbisub :
          bi ⊆
            ((Finset.univ.erase (Vertex.c0 cert)).erase
              (c1 cert)) := by
        intro p hp
        obtain ⟨w, hwtb, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hwtb).2
        have hrdata := hbdata hwtb
        have hr1 : r ≠ c1 cert := by
          intro hr1
          subst r
          have hmem : c1 cert ∈ cert.beta q := by
            rw [hbeta]
            simp
          exact ((cert.mem_beta (c1 cert) q).1 hmem) hrdata.2
        simp [hrdata.1, hr1]
      have heraseCard :
          ((Finset.univ.erase (Vertex.c0 cert)).erase
            (c1 cert) : Finset (Fin (k - 1))).card = k - 3 := by
        simp [c0_ne_c1.symm]
        have hk := cert.five_le_k
        omega
      have hle := Finset.card_le_card hbisub
      rw [hbiCard, heraseCard] at hle
      exact hle
    by_cases hy0 : ty.card = 0
    · have hk := cert.five_le_k
      omega
    · have hypos : 0 < ty.card := Nat.pos_of_ne_zero hy0
      obtain ⟨yw, hywty⟩ := Finset.card_pos.mp hypos
      obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hywty).2
      subst yw
      have hywt : Vertex.y cert r ∈ t :=
        (Finset.mem_filter.mp hywty).1
      have hcommon :=
        (finalGraph cert).mem_commonNeighbors.1 (htcommon hywt)
      obtain ⟨u, huS, hrEq⟩ :=
        y_common_mem_S_of_mem_E cert hG hqE hcommon.1 hcommon.2
      subst r
      obtain ⟨m, hm2, hmnon⟩ := missingLarge_of_mem_S huS
      have hm0 : m ≠ Vertex.c0 cert := by
        intro hm0
        have hv := congrArg Fin.val hm0
        simp [Vertex.c0, Certificates.c0Index] at hv
        omega
      have hm1 : m ≠ c1 cert := by
        intro hm1
        have hv := congrArg Fin.val hm1
        simp [c1, Certificates.c1Index] at hv
        omega
      have hbEY : tb.card ≤ k - 4 := by
        have hbeta := cert.beta_eq_c1_of_mem_E hG hqE
        have hbisub :
            bi ⊆
              (((Finset.univ.erase (Vertex.c0 cert)).erase
                (c1 cert)).erase m) := by
          intro p hp
          obtain ⟨w, hwtb, rfl⟩ := Finset.mem_image.mp hp
          obtain ⟨v, rfl⟩ := (Finset.mem_filter.mp hwtb).2
          have hvdata := hbdata hwtb
          have hv1 : v ≠ c1 cert := by
            intro hv1
            subst v
            have hmem : c1 cert ∈ cert.beta q := by
              rw [hbeta]
              simp
            exact ((cert.mem_beta (c1 cert) q).1 hmem) hvdata.2
          have hvm : v ≠ m := by
            intro hvm
            subst v
            have hym :=
              (final_y_b_of_ne_c0 cert u m hvdata.1).1
                (ht.isClique hywt
                  (Finset.mem_filter.mp hwtb).1 (by simp))
            exact hmnon hym
          simp [hvdata.1, hv1, hvm]
        have heraseCard :
            (((Finset.univ.erase (Vertex.c0 cert)).erase
              (c1 cert)).erase m :
                Finset (Fin (k - 1))).card = k - 4 := by
          simp [c0_ne_c1.symm, hm0, hm1]
          have hk := cert.five_le_k
          omega
        have hle := Finset.card_le_card hbisub
        rw [hbiCard, heraseCard] at hle
        exact hle
      have hk := cert.five_le_k
      omega
  · have hqS : q ∈ cert.S :=
      (cert.mem_S q).2 ⟨hqT, hqE⟩
    have hbS : tb.card ≤ k - 4 := by
      by_cases hb0 : tb.card = 0
      · have hk := cert.five_le_k
        omega
      · have hbpos : 0 < tb.card := Nat.pos_of_ne_zero hb0
        obtain ⟨bw, hbwtb⟩ := Finset.card_pos.mp hbpos
        obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hbwtb).2
        subst bw
        have hpdata := hbdata hbwtb
        by_cases hp2 : 2 ≤ p.val
        · have hlarge :
              ∀ {r : Fin (k - 1)}, Vertex.b r ∈ tb →
                2 ≤ r.val := by
            intro r hr
            by_cases hrp : r = p
            · simpa [hrp] using hp2
            · have hrdata := hbdata hr
              have hpr :=
                (final_b_b_of_ne_c0 cert p r hpdata.1 hrdata.1).1
                  (ht.isClique (Finset.mem_filter.mp hbwtb).1
                    (Finset.mem_filter.mp hr).1
                    (by simpa using Ne.symm hrp))
              rcases hpr.2 with hsmall | hlarge
              · omega
              · exact hlarge.2
          obtain ⟨m, hm2, hmnon⟩ := missingLarge_of_mem_S hqS
          have hm0 : m ≠ Vertex.c0 cert := by
            intro hm0
            have hv := congrArg Fin.val hm0
            simp [Vertex.c0, Certificates.c0Index] at hv
            omega
          have hm1 : m ≠ c1 cert := by
            intro hm1
            have hv := congrArg Fin.val hm1
            simp [c1, Certificates.c1Index] at hv
            omega
          have hbisub :
              bi ⊆
                (((Finset.univ.erase (Vertex.c0 cert)).erase
                  (c1 cert)).erase m) := by
            intro r hr
            obtain ⟨w, hwtb, rfl⟩ := Finset.mem_image.mp hr
            obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hwtb).2
            have hudata := hbdata hwtb
            have hu2 := hlarge hwtb
            have hu1 : u ≠ c1 cert := by
              intro hu1
              have hv := congrArg Fin.val hu1
              simp [c1, Certificates.c1Index] at hv
              omega
            have hum : u ≠ m := by
              intro hum
              subst u
              exact hmnon hudata.2
            simp [hudata.1, hu1, hum]
          have heraseCard :
              (((Finset.univ.erase (Vertex.c0 cert)).erase
                (c1 cert)).erase m :
                  Finset (Fin (k - 1))).card = k - 4 := by
            simp [c0_ne_c1.symm, hm0, hm1]
            have hk := cert.five_le_k
            omega
          have hle := Finset.card_le_card hbisub
          rw [hbiCard, heraseCard] at hle
          exact hle
        · have hpLt : p.val < 2 := Nat.lt_of_not_ge hp2
          have hall :
              ∀ {r : Fin (k - 1)}, Vertex.b r ∈ tb → r = p := by
            intro r hr
            by_cases hrp : r = p
            · exact hrp
            · have hrdata := hbdata hr
              have hpr :=
                (final_b_b_of_ne_c0 cert p r hpdata.1 hrdata.1).1
                  (ht.isClique (Finset.mem_filter.mp hbwtb).1
                    (Finset.mem_filter.mp hr).1
                    (by simpa using Ne.symm hrp))
              have hrLt : r.val < 2 := by
                rcases hpr.2 with hsmall | hlarge
                · exact hsmall.2
                · omega
              apply Fin.ext
              have hp0val : p.val ≠ 0 := by
                intro hp0val
                apply hpdata.1
                apply Fin.ext
                simpa [Vertex.c0, Certificates.c0Index] using hp0val
              have hr0val : r.val ≠ 0 := by
                intro hr0val
                apply hrdata.1
                apply Fin.ext
                simpa [Vertex.c0, Certificates.c0Index] using hr0val
              omega
          have hbOne : tb.card ≤ 1 := by
            rw [Finset.card_le_one_iff]
            intro u v hu hv
            obtain ⟨r, rfl⟩ := (Finset.mem_filter.mp hu).2
            obtain ⟨z, rfl⟩ := (Finset.mem_filter.mp hv).2
            rw [hall hu, hall hv]
          have hk := cert.five_le_k
          omega
    have hk := cert.five_le_k
    omega

end Switching
end RamseyIncrement
