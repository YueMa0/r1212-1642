/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.ChangedEdges
import Mathlib.Tactic

/-!
# Blue switching rows B4 and B5

This file proves the two blue row-safety statements whose switched edges
meet an ordinary `X` vertex:

* (B4), `z x_q` for `q ≠ 1`;
* (B5), `a₀ x_q` for `q ∈ E`.
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

private theorem pre_blue_adj_x_lower_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) (v : SpecialLiftVertex V k) :
    (preGraph cert)ᶜ.Adj (Vertex.x cert r) (.inl (.core v)) ↔
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r = v := by
  simp [preGraph, canonicalGraph, Canonical.graph, Vertex.x,
    redJoinedClone]
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
    and_comm, and_assoc]

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
    Vertex.i1, and_comm]

private theorem blue_adj_x_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (BlueGraph cert).Adj (Vertex.x cert r) (Vertex.y cert t) ↔
      r ≠ t := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.x, Vertex.y, redJoinedClone]

private theorem blue_adj_z_core_iff
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (BlueGraph cert).Adj Vertex.z (Vertex.core v) ↔
      v = cert.c (Vertex.c0 cert) ∨
        ¬G.Adj (cert.c (Vertex.c0 cert)) v := by
  have hb :
      (preGraph cert).Adj
          (Vertex.b (Vertex.c0 cert)) (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
    rw [preGraph_adj_lower_lower_iff]
    exact specialLift_adj_b_core G cert.c (Vertex.c0 cert) v
  have hpre :
      (preGraph cert).Adj Vertex.z (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
    simpa [preGraph, redJoinedClone] using hb
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]
  tauto

private theorem blue_adj_z_a_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (BlueGraph cert).Adj Vertex.z (Vertex.a p) ↔
      p = Vertex.c0 cert := by
  have hb :
      (preGraph cert).Adj
          (Vertex.b (Vertex.c0 cert)) (Vertex.a p) ↔
        p ≠ Vertex.c0 cert := by
    rw [preGraph_adj_lower_lower_iff]
    simpa [ne_comm] using
      (specialLift_adj_b_a G cert.c (Vertex.c0 cert) p)
  have hpre :
      (preGraph cert).Adj Vertex.z (Vertex.a p) ↔
        p ≠ Vertex.c0 cert := by
    simpa [preGraph, redJoinedClone] using hb
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_z_xSome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj Vertex.z (Vertex.x cert (some q)) ↔
      q ≠ Vertex.i1 cert := by
  rw [final_compl_adj_iff]
  simp [preGraph_adj_z_x cert (some q), removedRedGraph_adj_z_x_iff,
    addedRedGraph_adj_iff, SymmPair]

private theorem not_blue_adj_z_xNone
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(BlueGraph cert).Adj Vertex.z (Vertex.x cert none) := by
  rw [final_compl_adj_iff]
  simp [preGraph_adj_z_x cert none, removedRedGraph_adj_iff,
    addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_z_ySome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj Vertex.z (Vertex.y cert (some q)) ↔
      q ∈ cert.U := by
  have hpre :
      (preGraph cert).Adj Vertex.z (Vertex.y cert (some q)) ↔
        q ∈ cert.T := by
    have hb := preGraph_adj_b0_y_iff cert q
    simpa [preGraph, redJoinedClone] using hb
  rw [final_compl_adj_iff]
  simp [hpre, cert.mem_U, removedRedGraph_adj_iff,
    addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_z_yNone
    (cert : Certificates.OrderedCertificates G k s) :
    (BlueGraph cert).Adj Vertex.z (Vertex.y cert none) := by
  have hpre :
      ¬(preGraph cert).Adj Vertex.z (Vertex.y cert none) := by
    simpa [preGraph, redJoinedClone] using preGraph_not_adj_b0_yStar cert
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_a0_core_iff
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.core v) ↔
      v ≠ cert.c (Vertex.c0 cert) := by
  have hpre :
      (preGraph cert).Adj
          (Vertex.a (Vertex.c0 cert)) (Vertex.core v) ↔
        cert.c (Vertex.c0 cert) = v := by
    rw [preGraph_adj_lower_lower_iff]
    exact specialLift_adj_a_core G cert.c (Vertex.c0 cert) v
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff,
    SymmPair, ne_comm]

private theorem blue_adj_a0_b_iff
    (cert : Certificates.OrderedCertificates G k s)
    (p : Fin (k - 1)) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.b p) ↔
      p = Vertex.c0 cert := by
  have hpre :
      (preGraph cert).Adj
          (Vertex.a (Vertex.c0 cert)) (Vertex.b p) ↔
        Vertex.c0 cert ≠ p := by
    rw [preGraph_adj_lower_lower_iff]
    exact specialLift_adj_a_b G cert.c (Vertex.c0 cert) p
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff,
    SymmPair, eq_comm]

private theorem blue_adj_a0_xSome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert (some q)) ↔
      q ∈ cert.E := by
  rw [final_compl_adj_iff]
  simp [preGraph_adj_a0_x cert q, removedRedGraph_adj_a0_x_iff,
    addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_a0_xNone
    (cert : Certificates.OrderedCertificates G k s) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert none) := by
  have hpre :
      ¬(preGraph cert).Adj
        (Vertex.a (Vertex.c0 cert)) (Vertex.x cert none) := by
    rw [preGraph_adj_lower_x_iff]
    simp [Canonical.secondCertificateAt]
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_a0_ySome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
      q ∈ cert.U := by
  rw [final_compl_adj_iff]
  simp [preGraph_not_adj_a0_y cert q, cert.mem_U,
    addedRedGraph_adj_a0_y_iff, removedRedGraph_adj_iff, SymmPair]

private theorem not_blue_adj_a0_yNone
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert none) := by
  have hpre :
      (preGraph cert).Adj
        (Vertex.a (Vertex.c0 cert)) (Vertex.y cert none) := by
    rw [preGraph_adj_lower_y_iff]
    simp [Canonical.secondCertificateAt]
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_a0_z
    (cert : Certificates.OrderedCertificates G k s) :
    (BlueGraph cert).Adj (Vertex.a (Vertex.c0 cert)) Vertex.z := by
  rw [(BlueGraph cert).adj_comm]
  exact (blue_adj_z_a_iff cert (Vertex.c0 cert)).2 rfl

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

private theorem blue_adj_ySome_yNone_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj
        (Vertex.y cert (some q)) (Vertex.y cert none) ↔
      2 ≤ q.val ∨ (q = Vertex.i1 cert ∧ cert.E.Nonempty) := by
  have hpre :
      (preGraph cert).Adj
          (Vertex.y cert (some q)) (Vertex.y cert none) ↔
        q.val < 2 := by
    rw [preGraph_adj_y_y_iff]
    simp [Canonical.outerIndexEquiv, SameBPart]
    have hs := cert.five_le_s
    omega
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff,
    SymmPair, Vertex.i1]
  constructor
  · rintro (hq | ⟨hE, hq1⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hq1, hE⟩
  · rintro (hq | ⟨hq1, hE⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hE, hq1⟩

private theorem blue_adj_ySome_yNone_large_of_mem_U
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqU : q ∈ cert.U)
    (h : (BlueGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.y cert none)) :
    2 ≤ q.val := by
  rcases (blue_adj_ySome_yNone_iff cert q).1 h with hlarge | ⟨hq1, hE⟩
  · exact hlarge
  · have hi1T := cert.E_subset_T ((cert.E_nonempty_iff_i1_mem hG).1 hE)
    exact False.elim (((cert.mem_U q).1 hqU)
      (by simpa [hq1] using hi1T))

private theorem not_blue_adj_xNone_core
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    ¬(BlueGraph cert).Adj (Vertex.x cert none) (Vertex.core v) := by
  have hpre := pre_blue_adj_x_lower_iff cert none
    (SpecialLiftVertex.core v)
  simp [SimpleGraph.compl_adj, Canonical.secondCertificateAt] at hpre
  simp [BlueGraph, finalGraph, removedRedGraph, removedRedRel,
    addedRedGraph, addedRedRel, hpre, Vertex.x, Vertex.core]

private theorem blue_adj_b0_core_iff
    (cert : Certificates.OrderedCertificates G k s) (v : V) :
    (BlueGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.core v) ↔
      v = cert.c (Vertex.c0 cert) ∨
        ¬G.Adj (cert.c (Vertex.c0 cert)) v := by
  have hpre :
      (preGraph cert).Adj
          (Vertex.b (Vertex.c0 cert)) (Vertex.core v) ↔
        v ≠ cert.c (Vertex.c0 cert) ∧
          G.Adj (cert.c (Vertex.c0 cert)) v := by
    rw [preGraph_adj_lower_lower_iff]
    exact specialLift_adj_b_core G cert.c (Vertex.c0 cert) v
  rw [final_compl_adj_iff]
  simp [hpre, removedRedGraph_adj_iff, addedRedGraph_adj_iff, SymmPair]
  tauto

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
          ⟨Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              (cert.five_le_s)) r, ?_⟩)))
        simp [Vertex.x]
    | b r =>
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              (cert.five_le_s)) r, ?_⟩))))
        simp [Vertex.y]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private theorem caseB_U_small_eq_i0
    (cert : Certificates.OrderedCertificates G k s)
    (hB : Certificates.CaseBData cert.toCertificates cert.five_le_k)
    {q : Fin (s - 1)} (hqU : q ∈ cert.U) (hqsmall : q.val < 2) :
    q = Certificates.i0Index' cert.five_le_s := by
  have hi1T := cert.E_subset_T (cert.caseB_i1_mem_E hB)
  have hqNotT := (cert.mem_U q).1 hqU
  apply Fin.ext
  simp
  by_cases hq0 : q.val = 0
  · exact hq0
  · have hq1 : q = Vertex.i1 cert := by
      apply Fin.ext
      simp [Vertex.i1]
      omega
    exact False.elim (hqNotT (by simpa [hq1] using hi1T))

private theorem caseB_E_ne_i1_large
    (cert : Certificates.OrderedCertificates G k s)
    (hB : Certificates.CaseBData cert.toCertificates cert.five_le_k)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E)
    (hq1 : q ≠ Vertex.i1 cert) :
    2 ≤ q.val := by
  by_contra hq2
  have hqsmall : q.val < 2 := by omega
  by_cases hq0 : q.val = 0
  · have hqi0 :
        q = Certificates.i0Index' cert.five_le_s := by
      apply Fin.ext
      simpa using hq0
    have hi0U := cert.caseB_i0_mem_U hB
    have hqT := cert.E_subset_T hqE
    exact ((cert.mem_U q).1 (by simpa [hqi0] using hi0U)) hqT
  · apply hq1
    apply Fin.ext
    simp [Vertex.i1]
    omega

private theorem card_E_erase_le_ELarge
    (cert : Certificates.OrderedCertificates G k s)
    (hB : Certificates.CaseBData cert.toCertificates cert.five_le_k)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) :
    (cert.E.erase q).card ≤ cert.ELarge.card := by
  have hsub :
      cert.E ⊆ insert (Vertex.i1 cert) cert.ELarge := by
    intro r hrE
    by_cases hr1 : r = Vertex.i1 cert
    · simp [hr1]
    · exact Finset.mem_insert_of_mem
        ((cert.mem_ELarge r).2
          ⟨hrE, caseB_E_ne_i1_large cert hB hrE hr1⟩)
  have hcard := Finset.card_le_card hsub
  have herase := Finset.card_erase_of_mem hqE
  have hinsert := Finset.card_insert_le
    (Vertex.i1 cert) cert.ELarge
  omega

private def xSomeEmbedding
    (cert : Certificates.OrderedCertificates G k s) :
    Fin (s - 1) ↪ Vertex V k s where
  toFun q := Vertex.x cert (some q)
  inj' := by
    intro q r h
    have houter :
        (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm (some q) =
        (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm (some r) :=
      SpecialLiftVertex.a.inj (Sum.inl.inj h)
    exact Option.some.inj
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s))).symm.injective houter)

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

private noncomputable def xSet
    (cert : Certificates.OrderedCertificates G k s)
    (P : Finset (Fin (s - 1))) : Finset (Vertex V k s) :=
  P.map (xSomeEmbedding cert)

private noncomputable def ySet
    (cert : Certificates.OrderedCertificates G k s)
    (Q : Finset (Fin (s - 1))) : Finset (Vertex V k s) :=
  Q.map (ySomeEmbedding cert)

@[simp]
private theorem mem_xSet
    (cert : Certificates.OrderedCertificates G k s)
    (P : Finset (Fin (s - 1))) (q : Fin (s - 1)) :
    Vertex.x cert (some q) ∈ xSet cert P ↔ q ∈ P := by
  constructor
  · intro h
    obtain ⟨r, hr, heq⟩ := Finset.mem_map.1 h
    have hrq : r = q := (xSomeEmbedding cert).injective heq
    simpa [hrq] using hr
  · intro h
    exact Finset.mem_map.2 ⟨q, h, rfl⟩

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
private theorem card_xSet
    (cert : Certificates.OrderedCertificates G k s)
    (P : Finset (Fin (s - 1))) :
    (xSet cert P).card = P.card := by
  simp [xSet]

@[simp]
private theorem card_ySet
    (cert : Certificates.OrderedCertificates G k s)
    (Q : Finset (Fin (s - 1))) :
    (ySet cert Q).card = Q.card := by
  simp [ySet]

private theorem card_le_one_add_xSet_ySet
    [DecidableEq V]
    {cert : Certificates.OrderedCertificates G k s}
    {K : Finset (Vertex V k s)} {e : Vertex V k s}
    {P Q : Finset (Fin (s - 1))}
    (hsub : K ⊆ insert e (xSet cert P ∪ ySet cert Q)) :
    K.card ≤ 1 + P.card + Q.card := by
  have hK := Finset.card_le_card hsub
  have hins := Finset.card_insert_le e (xSet cert P ∪ ySet cert Q)
  have hunion := Finset.card_union_le (xSet cert P) (ySet cert Q)
  rw [card_xSet, card_ySet] at hunion
  omega

private theorem card_le_two_add_xSet_ySet
    [DecidableEq V]
    {cert : Certificates.OrderedCertificates G k s}
    {K : Finset (Vertex V k s)} {e₁ e₂ : Vertex V k s}
    {P Q : Finset (Fin (s - 1))}
    (hsub : K ⊆ insert e₁ (insert e₂ (xSet cert P ∪ ySet cert Q))) :
    K.card ≤ 2 + P.card + Q.card := by
  have hK := Finset.card_le_card hsub
  have hins₁ :=
    Finset.card_insert_le e₁ (insert e₂ (xSet cert P ∪ ySet cert Q))
  have hins₂ := Finset.card_insert_le e₂ (xSet cert P ∪ ySet cert Q)
  have hunion := Finset.card_union_le (xSet cert P) (ySet cert Q)
  rw [card_xSet, card_ySet] at hunion
  omega

private theorem common_z_xSome_cases
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)} (hq1 : q ≠ Vertex.i1 cert)
    {w : Vertex V k s}
    (hz : (BlueGraph cert).Adj Vertex.z w)
    (hx : (BlueGraph cert).Adj (Vertex.x cert (some q)) w) :
    (q ∈ cert.U ∧ w = Vertex.core (cert.i q)) ∨
      (q ∈ cert.E ∧ w = Vertex.a (Vertex.c0 cert)) ∨
      (∃ r : Fin (s - 1),
        r ≠ Vertex.i1 cert ∧ r ≠ q ∧
          w = Vertex.x cert (some r)) ∨
      w = Vertex.y cert none ∨
      (∃ r : Fin (s - 1), r ∈ cert.U ∧ r ≠ q ∧
        w = Vertex.y cert (some r)) := by
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    have hv := (blue_adj_xSome_core_iff cert q v).1 hx
    subst v
    left
    refine ⟨(cert.mem_U q).2 ?_, rfl⟩
    intro hqT
    rcases (blue_adj_z_core_iff cert (cert.i q)).1 hz with heq | hn
    · exact cert.c_ne_i (Vertex.c0 cert) q heq.symm
    · exact hn ((cert.mem_T q).1 hqT)
  · obtain ⟨p, rfl⟩ := h
    have hp := (blue_adj_xSome_a_iff cert q p).1 hx
    exact Or.inr (Or.inl ⟨hp.1, by simp [hp.2]⟩)
  · obtain ⟨p, rfl⟩ := h
    have hqi := (blue_adj_xSome_b_iff cert q p).1 hx |>.1
    exact False.elim (hq1 hqi)
  · obtain ⟨r, rfl⟩ := h
    cases r with
    | none => exact False.elim (not_blue_adj_z_xNone cert hz)
    | some r =>
        right; right; left
        exact ⟨r, (blue_adj_z_xSome_iff cert r).1 hz,
          fun hrq ↦
            (blue_adj_x_x_iff cert (some q) (some r)).1 hx
              (congrArg some hrq.symm),
          rfl⟩
  · obtain ⟨r, rfl⟩ := h
    cases r with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | some r =>
        right; right; right; right
        exact ⟨r, (blue_adj_z_ySome_iff cert r).1 hz,
          fun hrq ↦
            (blue_adj_x_y_iff cert (some q) (some r)).1 hx
              (congrArg some hrq.symm),
          rfl⟩
  · subst w
    exact False.elim ((BlueGraph cert).loopless.irrefl _ hz)

private theorem common_a0_xSome_cases
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)}
    {w : Vertex V k s}
    (ha : (BlueGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) w)
    (hx : (BlueGraph cert).Adj (Vertex.x cert (some q)) w) :
    w = Vertex.core (cert.i q) ∨
      (q = Vertex.i1 cert ∧
        w = Vertex.b (Vertex.c0 cert)) ∨
      (∃ r : Fin (s - 1), r ∈ cert.E ∧ r ≠ q ∧
        w = Vertex.x cert (some r)) ∨
      w = Vertex.x cert none ∨
      (∃ r : Fin (s - 1), r ∈ cert.U ∧
        w = Vertex.y cert (some r)) ∨
      (q ≠ Vertex.i1 cert ∧ w = Vertex.z) := by
  rcases vertex_cases cert w with h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    exact Or.inl (by
      have hv := (blue_adj_xSome_core_iff cert q v).1 hx
      simpa [hv])
  · obtain ⟨p, rfl⟩ := h
    have hp := (blue_adj_xSome_a_iff cert q p).1 hx |>.2
    subst p
    exact False.elim ((BlueGraph cert).loopless.irrefl _ ha)
  · obtain ⟨p, rfl⟩ := h
    have hp := (blue_adj_xSome_b_iff cert q p).1 hx
    exact Or.inr (Or.inl ⟨hp.1, by simp [hp.2]⟩)
  · obtain ⟨r, rfl⟩ := h
    cases r with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | some r =>
        right; right; left
        exact ⟨r, (blue_adj_a0_xSome_iff cert r).1 ha,
          fun hrq ↦
            (blue_adj_x_x_iff cert (some q) (some r)).1 hx
              (congrArg some hrq.symm),
          rfl⟩
  · obtain ⟨r, rfl⟩ := h
    cases r with
    | none => exact False.elim (not_blue_adj_a0_yNone cert ha)
    | some r =>
        right; right; right; right; left
        exact ⟨r, (blue_adj_a0_ySome_iff cert r).1 ha, rfl⟩
  · subst w
    right; right; right; right; right
    exact ⟨(blue_adj_z_xSome_iff cert q).1
      ((BlueGraph cert).adj_symm hx), rfl⟩

private def xyIndex
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → Option (Fin (s - 1))
  | .inl (.a r) =>
      Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r
  | .inl (.b r) =>
      Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          (cert.five_le_s)) r
  | _ => none

@[simp]
private theorem xyIndex_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    xyIndex cert (Vertex.x cert r) = r := by
  simp [xyIndex, Vertex.x]

@[simp]
private theorem xyIndex_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    xyIndex cert (Vertex.y cert r) = r := by
  simp [xyIndex, Vertex.y]

private theorem card_xy_common_z_xSome_le
    [DecidableEq V]
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hq1 : q ≠ Vertex.i1 cert)
    {K : Finset (Vertex V k s)}
    (hK : (BlueGraph cert).IsClique (K : Set (Vertex V k s)))
    (hclass :
      ∀ w ∈ K,
        (∃ r : Fin (s - 1),
          r ≠ Vertex.i1 cert ∧ r ≠ q ∧
            w = Vertex.x cert (some r)) ∨
        w = Vertex.y cert none ∨
        (∃ r : Fin (s - 1), r ∈ cert.U ∧ r ≠ q ∧
          w = Vertex.y cert (some r))) :
    K.card ≤ s - 2 := by
  let I : Finset (Option (Fin (s - 1))) :=
    K.image (xyIndex cert)
  have hinj : Set.InjOn (xyIndex cert) K := by
    intro u hu v hv huv
    rcases hclass u hu with
        ⟨r, hr1, hrq, rfl⟩ | rfl | ⟨r, hrU, hrq, rfl⟩
    · rcases hclass v hv with
          ⟨t, ht1, htq, rfl⟩ | rfl | ⟨t, htU, htq, rfl⟩
      · have hrt : r = t := by simpa using huv
        subst t
        rfl
      · simp at huv
      · have hrt : r = t := by simpa using huv
        subst t
        exact False.elim <|
          (blue_adj_x_y_iff cert (some r) (some r)).1
            (hK hu hv (by simp)) rfl
    · rcases hclass v hv with
          ⟨t, ht1, htq, rfl⟩ | rfl | ⟨t, htU, htq, rfl⟩
      · simp at huv
      · rfl
      · simp at huv
    · rcases hclass v hv with
          ⟨t, ht1, htq, rfl⟩ | rfl | ⟨t, htU, htq, rfl⟩
      · have hrt : r = t := by simpa using huv
        subst t
        exact False.elim <|
          (blue_adj_x_y_iff cert (some r) (some r)).1
            ((BlueGraph cert).adj_symm (hK hu hv (by simp))) rfl
      · simp at huv
      · have hrt : r = t := by simpa using huv
        subst t
        rfl
  have hIcard : I.card = K.card := by
    dsimp [I]
    rw [Finset.card_image_of_injOn hinj]
  have hqnot : some q ∉ I := by
    intro hqI
    obtain ⟨w, hwK, hwq⟩ := Finset.mem_image.mp hqI
    rcases hclass w hwK with
        ⟨r, hr1, hrq, hrw⟩ | hrw | ⟨r, hrU, hrq, hrw⟩
    · subst w
      have hr : r = q := by simpa using hwq
      exact hrq hr
    · subst w
      simp at hwq
    · subst w
      have hr : r = q := by simpa using hwq
      exact hrq hr
  by_cases hyStar : Vertex.y cert none ∈ K
  · have hi1not : some (Vertex.i1 cert) ∉ I := by
      intro hiI
      obtain ⟨w, hwK, hwi⟩ := Finset.mem_image.mp hiI
      rcases hclass w hwK with
          ⟨r, hr1, hrq, hrw⟩ | hrw | ⟨r, hrU, hrq, hrw⟩
      · subst w
        have hr : r = Vertex.i1 cert := by simpa using hwi
        exact hr1 hr
      · subst w
        simp at hwi
      · subst w
        have hr : r = Vertex.i1 cert := by simpa using hwi
        subst r
        have hadj :=
          hK hwK hyStar (by simp [Vertex.y])
        have hlarge :=
          blue_adj_ySome_yNone_large_of_mem_U cert hG hrU hadj
        have hi1val : (Vertex.i1 cert).val = 1 := rfl
        omega
    have hsub :
        I ⊆
          ((Finset.univ.erase (some q)).erase
            (some (Vertex.i1 cert))) := by
      intro r hr
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h ↦ hi1not (by simpa [h] using hr),
        fun h ↦ hqnot (by simpa [h] using hr)⟩
    have hcard := Finset.card_le_card hsub
    have htarget :
        ((Finset.univ.erase (some q)).erase
          (some (Vertex.i1 cert)) :
          Finset (Option (Fin (s - 1)))).card = s - 2 := by
      have hs := cert.five_le_s
      rw [Finset.card_erase_of_mem (by simp [hq1.symm]),
        Finset.card_erase_of_mem (Finset.mem_univ (some q))]
      simp
      omega
    rw [hIcard, htarget] at hcard
    exact hcard
  · have hnonenot : none ∉ I := by
      intro hnI
      obtain ⟨w, hwK, hwn⟩ := Finset.mem_image.mp hnI
      rcases hclass w hwK with
          ⟨r, hr1, hrq, hrw⟩ | hrw | ⟨r, hrU, hrq, hrw⟩
      · subst w
        simp at hwn
      · exact hyStar (by simpa [hrw] using hwK)
      · subst w
        simp at hwn
    have hsub :
        I ⊆ ((Finset.univ.erase (some q)).erase none) := by
      intro r hr
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h ↦ hnonenot (by simpa [h] using hr),
        fun h ↦ hqnot (by simpa [h] using hr)⟩
    have hcard := Finset.card_le_card hsub
    have htarget :
        ((Finset.univ.erase (some q)).erase none :
          Finset (Option (Fin (s - 1)))).card = s - 2 := by
      have hs := cert.five_le_s
      simp
      omega
    rw [hIcard, htarget] at hcard
    exact hcard

/-- Row (B4): every switched edge `z x_q`, for ordinary `q ≠ 1`,
is blue-safe. -/
theorem blue_case_b4
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hq1 : q ≠ Vertex.i1 cert) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        Vertex.z (Vertex.x cert (some q))) (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj Vertex.z w ∧
        (BlueGraph cert).Adj (Vertex.x cert (some q)) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hclass {w : Vertex V k s} (hw : w ∈ K) :=
    common_z_xSome_cases cert hq1 (hcommon hw).1 (hcommon hw).2
  by_cases hiq : Vertex.core (cert.i q) ∈ K
  · have hqU : q ∈ cert.U := by
      rcases hclass hiq with hi | ha | hx | hy | hy
      · exact hi.1
      · simp at ha
      · obtain ⟨_, _, _, hfalse⟩ := hx
        simp at hfalse
      · simp at hy
      · obtain ⟨_, _, _, hfalse⟩ := hy
        simp at hfalse
    have hreduced (w : Vertex V k s) (hw : w ∈ K) :
        w = Vertex.core (cert.i q) ∨
          w = Vertex.y cert none ∨
          (∃ r : Fin (s - 1), r ∈ cert.U ∧ r ≠ q ∧
            w = Vertex.y cert (some r)) := by
      rcases hclass hw with hi | ha | hx | hy | hy
      · exact Or.inl hi.2
      · have hqT := cert.E_subset_T ha.1
        exact False.elim (((cert.mem_U q).1 hqU) hqT)
      · obtain ⟨r, hr1, hrq, hrw⟩ := hx
        have hadj :=
          (BlueGraph cert).adj_symm
            (hK.isClique hiq hw (by simpa [hrw]))
        have heq :=
          (blue_adj_xSome_core_iff cert r (cert.i q)).1
            (by simpa [hrw] using hadj)
        exact False.elim (hrq (cert.i.injective heq).symm)
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr hy)
    by_cases hq0 : q.val = 0
    · have hqi0 :
          q = Certificates.i0Index' cert.five_le_s := by
        apply Fin.ext
        simpa using hq0
      have hB :
          Certificates.CaseBData cert.toCertificates cert.five_le_k := by
        rcases cert.normal with hA | hB
        · have hi0S := cert.caseA_i0_mem_S hG hA
          have hi0T := cert.S_subset_T hi0S
          exact False.elim (((cert.mem_U q).1 hqU)
            (by simpa [hqi0] using hi0T))
        · exact hB
      have hYlarge (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) :
          r ∈ cert.ULarge := by
        rcases hreduced _ hrK with hi | hy | hy
        · simp at hi
        · simp at hy
        · obtain ⟨t, htU, htq, heq⟩ := hy
          have htr : t = r := (ySomeEmbedding cert).injective heq.symm
          subst t
          apply (cert.mem_ULarge r).2
          refine ⟨htU, ?_⟩
          by_contra hr2
          have hre := caseB_U_small_eq_i0 cert hB htU (by omega)
          exact htq (hre.trans hqi0.symm)
      have hsub :
          K ⊆
            insert (Vertex.core (cert.i q))
              (insert (Vertex.y cert none)
                (xSet cert ∅ ∪ ySet cert cert.ULarge)) := by
        intro w hw
        rcases hreduced w hw with hi | hy | ⟨r, hrU, hrq, rfl⟩
        · simpa [hi]
        · simpa [hy]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                ((mem_ySet cert cert.ULarge r).2
                  (hYlarge r hw))))
      have hcard :=
        card_le_two_add_xSet_ySet
          (cert := cert) (K := K)
          (e₁ := Vertex.core (cert.i q))
          (e₂ := Vertex.y cert none)
          (P := ∅) (Q := cert.ULarge) hsub
      have hUL := cert.caseB_card_ULarge_le hB
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hks := hB.k_le_s
      simp at hcard
      omega
    · have hq2 : 2 ≤ q.val := by
        have hqval1 : q.val ≠ 1 := by
          intro h
          apply hq1
          apply Fin.ext
          simpa [Vertex.i1] using h
        omega
      have hqLarge : q ∈ cert.largeIndices :=
        (cert.mem_largeIndices_iff q).2 hq2
      let Qlarge := cert.largeIndices.erase q
      have hQcard : Qlarge.card = s - 4 := by
        dsimp [Qlarge]
        rw [Finset.card_erase_of_mem hqLarge, cert.card_largeIndices]
        have hs := cert.five_le_s
        omega
      by_cases hyStar : Vertex.y cert none ∈ K
      · have hYlarge (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) :
            r ∈ Qlarge := by
          rcases hreduced _ hrK with hi | hy | hy
          · simp at hi
          · simp at hy
          · obtain ⟨t, htU, htq, heq⟩ := hy
            have htr : t = r := (ySomeEmbedding cert).injective heq.symm
            subst t
            rw [Finset.mem_erase]
            exact ⟨htq, (cert.mem_largeIndices_iff r).2
              (blue_adj_ySome_yNone_large_of_mem_U cert hG htU
                (hK.isClique hrK hyStar (by simp [Vertex.y])))⟩
        have hsub :
            K ⊆
              insert (Vertex.core (cert.i q))
                (insert (Vertex.y cert none)
                  (xSet cert ∅ ∪ ySet cert Qlarge)) := by
          intro w hw
          rcases hreduced w hw with hi | hy | ⟨r, hrU, hrq, rfl⟩
          · simpa [hi]
          · simpa [hy]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem
                (Finset.mem_union_right _
                  ((mem_ySet cert Qlarge r).2 (hYlarge r hw))))
        have hcard :=
          card_le_two_add_xSet_ySet
            (cert := cert) (K := K)
            (e₁ := Vertex.core (cert.i q))
            (e₂ := Vertex.y cert none)
            (P := ∅) (Q := Qlarge) hsub
        have hcardK := hK.card_eq
        simp at hcard
        omega
      · by_cases hsmall :
          ∃ r : Fin (s - 1),
            Vertex.y cert (some r) ∈ K ∧ r.val < 2
        · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
          let Qsmall : Finset (Fin (s - 1)) :=
            {Certificates.i0Index' cert.five_le_s,
              Vertex.i1 cert}
          have hYsmall (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ Qsmall := by
            have hrU : r ∈ cert.U := by
              rcases hreduced _ hrK with hi | hy | hy
              · simp at hi
              · simp at hy
              · obtain ⟨t, htU, htq, heq⟩ := hy
                exact (by
                  have htr : t = r := (ySomeEmbedding cert).injective heq.symm
                  simpa [htr] using htU)
            have hrsmall : r.val < 2 := by
              by_cases hrr : r₀ = r
              · simpa [← hrr] using hr₀small
              · have hadj := hK.isClique hr₀K hrK (by
                  intro heq
                  exact hrr ((ySomeEmbedding cert).injective heq))
                rcases blue_adj_ySome_same_part_of_mem_U cert hG
                    (by
                      rcases hreduced _ hr₀K with hi | hy | hy
                      · simp at hi
                      · simp at hy
                      · obtain ⟨t, htU, htq, heq⟩ := hy
                        have htr : t = r₀ :=
                          (ySomeEmbedding cert).injective heq.symm
                        simpa [htr] using htU)
                    hrU hadj with hs | hs
                · exact hs.2
                · omega
            have hr01 :
                r = Certificates.i0Index' cert.five_le_s ∨
                  r = Vertex.i1 cert := by
              by_cases hr0 : r.val = 0
              · left
                apply Fin.ext
                simpa using hr0
              · right
                apply Fin.ext
                simp [Vertex.i1]
                omega
            simpa [Qsmall] using hr01
          have hsub :
              K ⊆ insert (Vertex.core (cert.i q))
                (xSet cert ∅ ∪ ySet cert Qsmall) := by
            intro w hw
            rcases hreduced w hw with hi | hy | ⟨r, hrU, hrq, rfl⟩
            · simpa [hi]
            · exact False.elim (hyStar (by simpa [hy] using hw))
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_right _
                  ((mem_ySet cert Qsmall r).2 (hYsmall r hw)))
          have hcard :=
            card_le_one_add_xSet_ySet
              (cert := cert) (K := K)
              (e := Vertex.core (cert.i q))
              (P := ∅) (Q := Qsmall) hsub
          have hQ : Qsmall.card ≤ 2 := by
            dsimp [Qsmall]
            exact Finset.card_insert_le _ _
          have hcardK := hK.card_eq
          have hs := cert.five_le_s
          simp at hcard
          omega
        · have hYlarge (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ Qlarge := by
            rcases hreduced _ hrK with hi | hy | hy
            · simp at hi
            · simp at hy
            · obtain ⟨t, htU, htq, heq⟩ := hy
              have htr : t = r := (ySomeEmbedding cert).injective heq.symm
              subst t
              rw [Finset.mem_erase]
              exact ⟨htq, (cert.mem_largeIndices_iff r).2
                (by
                  by_contra hr2
                  exact hsmall ⟨r, hrK, by omega⟩)⟩
          have hsub :
              K ⊆ insert (Vertex.core (cert.i q))
                (xSet cert ∅ ∪ ySet cert Qlarge) := by
            intro w hw
            rcases hreduced w hw with hi | hy | ⟨r, hrU, hrq, rfl⟩
            · simpa [hi]
            · exact False.elim (hyStar (by simpa [hy] using hw))
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_right _
                  ((mem_ySet cert Qlarge r).2 (hYlarge r hw)))
          have hcard :=
            card_le_one_add_xSet_ySet
              (cert := cert) (K := K)
              (e := Vertex.core (cert.i q))
              (P := ∅) (Q := Qlarge) hsub
          have hcardK := hK.card_eq
          simp at hcard
          omega
  · by_cases ha0 : Vertex.a (Vertex.c0 cert) ∈ K
    · have hqE : q ∈ cert.E := by
        rcases hclass ha0 with hi | ha | hx | hy | hy
        · simp at hi
        · exact ha.1
        · obtain ⟨_, _, _, hfalse⟩ := hx
          simp at hfalse
        · simp at hy
        · obtain ⟨_, _, _, hfalse⟩ := hy
          simp at hfalse
      have hB :
          Certificates.CaseBData cert.toCertificates cert.five_le_k :=
        cert.caseBData_of_E_nonempty hG ⟨q, hqE⟩
      have hq2 := caseB_E_ne_i1_large cert hB hqE hq1
      have hqEL : q ∈ cert.ELarge :=
        (cert.mem_ELarge q).2 ⟨hqE, hq2⟩
      let P := cert.ELarge.erase q
      have hPcard : P.card + 1 = cert.ELarge.card := by
        dsimp [P]
        have h := Finset.card_erase_of_mem hqEL
        have hpos := Finset.card_pos.mpr ⟨q, hqEL⟩
        omega
      have hreduced (w : Vertex V k s) (hw : w ∈ K) :
          w = Vertex.a (Vertex.c0 cert) ∨
            (∃ r : Fin (s - 1), r ∈ P ∧
              w = Vertex.x cert (some r)) ∨
            (∃ r : Fin (s - 1), r ∈ cert.U ∧
              w = Vertex.y cert (some r)) := by
        rcases hclass hw with hi | ha | hx | hy | hy
        · exact False.elim (hiq (by simpa [hi.2] using hw))
        · exact Or.inl ha.2
        · obtain ⟨r, hr1, hrq, hrw⟩ := hx
          have hrK : Vertex.x cert (some r) ∈ K := by
            simpa [hrw] using hw
          have hrE :=
            (blue_adj_a0_xSome_iff cert r).1
              (hK.isClique ha0 hrK (by simp))
          have hr2 := caseB_E_ne_i1_large cert hB hrE hr1
          exact Or.inr (Or.inl
            ⟨r, by
              rw [Finset.mem_erase]
              exact ⟨hrq, (cert.mem_ELarge r).2 ⟨hrE, hr2⟩⟩,
              hrw⟩)
        · have hyK : Vertex.y cert none ∈ K := by
            simpa [hy] using hw
          exact False.elim <| not_blue_adj_a0_yNone cert
            (hK.isClique ha0 hyK (by simp))
        · obtain ⟨r, hrU, hrq, hrw⟩ := hy
          exact Or.inr (Or.inr ⟨r, hrU, hrw⟩)
      by_cases hsmall :
          ∃ r : Fin (s - 1),
            Vertex.y cert (some r) ∈ K ∧ r.val < 2
      · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
        let Qsmall : Finset (Fin (s - 1)) :=
          {Certificates.i0Index' cert.five_le_s}
        have hYsmall (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) :
            r ∈ Qsmall := by
          have hrU : r ∈ cert.U := by
            rcases hreduced _ hrK with ha | hx | hy
            · simp at ha
            · obtain ⟨_, _, hfalse⟩ := hx
              simp at hfalse
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r := (ySomeEmbedding cert).injective heq.symm
              simpa [htr] using htU
          have hrsmall : r.val < 2 := by
            by_cases hrr : r₀ = r
            · simpa [← hrr] using hr₀small
            · have hr₀U : r₀ ∈ cert.U := by
                rcases hreduced _ hr₀K with ha | hx | hy
                · simp at ha
                · obtain ⟨_, _, hfalse⟩ := hx
                  simp at hfalse
                · obtain ⟨t, htU, heq⟩ := hy
                  have htr : t = r₀ :=
                    (ySomeEmbedding cert).injective heq.symm
                  simpa [htr] using htU
              have hadj := hK.isClique hr₀K hrK (by
                intro heq
                exact hrr ((ySomeEmbedding cert).injective heq))
              rcases blue_adj_ySome_same_part_of_mem_U cert hG
                  hr₀U hrU hadj with hs | hs
              · exact hs.2
              · omega
          have hre := caseB_U_small_eq_i0 cert hB hrU hrsmall
          simp [Qsmall, hre]
        have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert))
              (xSet cert P ∪ ySet cert Qsmall) := by
          intro w hw
          rcases hreduced w hw with ha | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
          · simpa [ha]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _
                ((mem_xSet cert P r).2 hrP))
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                ((mem_ySet cert Qsmall r).2 (hYsmall r hw)))
        have hcard :=
          card_le_one_add_xSet_ySet
            (cert := cert) (K := K)
            (e := Vertex.a (Vertex.c0 cert))
            (P := P) (Q := Qsmall) hsub
        have hEL := cert.caseB_card_ELarge_le hB
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        simp [Qsmall] at hcard
        omega
      · have hYlarge (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) :
            r ∈ cert.ULarge := by
          rcases hreduced _ hrK with ha | hx | hy
          · simp at ha
          · obtain ⟨_, _, hfalse⟩ := hx
            simp at hfalse
          · obtain ⟨t, htU, heq⟩ := hy
            have htr : t = r := (ySomeEmbedding cert).injective heq.symm
            subst t
            exact (cert.mem_ULarge r).2 ⟨htU, by
              by_contra hr2
              exact hsmall ⟨r, hrK, by omega⟩⟩
        have hsub :
            K ⊆ insert (Vertex.a (Vertex.c0 cert))
              (xSet cert P ∪ ySet cert cert.ULarge) := by
          intro w hw
          rcases hreduced w hw with ha | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
          · simpa [ha]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _
                ((mem_xSet cert P r).2 hrP))
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                ((mem_ySet cert cert.ULarge r).2 (hYlarge r hw)))
        have hcard :=
          card_le_one_add_xSet_ySet
            (cert := cert) (K := K)
            (e := Vertex.a (Vertex.c0 cert))
            (P := P) (Q := cert.ULarge) hsub
        have hUL := cert.caseB_card_ULarge_le hB
        have hEL := cert.caseB_card_ELarge_le hB
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hks := hB.k_le_s
        omega
    · have hxy (w : Vertex V k s) (hw : w ∈ K) :
          (∃ r : Fin (s - 1),
            r ≠ Vertex.i1 cert ∧ r ≠ q ∧
              w = Vertex.x cert (some r)) ∨
          w = Vertex.y cert none ∨
          (∃ r : Fin (s - 1), r ∈ cert.U ∧ r ≠ q ∧
            w = Vertex.y cert (some r)) := by
        rcases hclass hw with hi | ha | hx | hy | hy
        · exact False.elim (hiq (by simpa [hi.2] using hw))
        · exact False.elim (ha0 (by simpa [ha.2] using hw))
        · exact Or.inl hx
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr hy)
      have hcard :=
        card_xy_common_z_xSome_le cert hG hq1 hK.isClique hxy
      have hcardK := hK.card_eq
      omega

/-- Row (B5): every switched edge `a₀ x_q`, for `q ∈ E`, is
blue-safe. -/
theorem blue_case_b5
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.a (Vertex.c0 cert))
        (Vertex.x cert (some q))) (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj (Vertex.a (Vertex.c0 cert)) w ∧
        (BlueGraph cert).Adj (Vertex.x cert (some q)) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hclass {w : Vertex V k s} (hw : w ∈ K) :=
    common_a0_xSome_cases cert (hcommon hw).1 (hcommon hw).2
  have hB :
      Certificates.CaseBData cert.toCertificates cert.five_le_k :=
    cert.caseBData_of_E_nonempty hG ⟨q, hqE⟩
  have hqT : q ∈ cert.T := cert.E_subset_T hqE
  by_cases hiq : Vertex.core (cert.i q) ∈ K
  · have hreduced (w : Vertex V k s) (hw : w ∈ K) :
        w = Vertex.core (cert.i q) ∨
          (∃ r : Fin (s - 1), r ∈ cert.U ∧
            w = Vertex.y cert (some r)) := by
      rcases hclass hw with hi | hb | hx | hxstar | hy | hz
      · exact Or.inl hi
      · obtain ⟨hq1, hrw⟩ := hb
        have hbK : Vertex.b (Vertex.c0 cert) ∈ K := by
          simpa [hrw] using hw
        have hadj :=
          (blue_adj_b0_core_iff cert (cert.i q)).1
            (hK.isClique hbK hiq (by simp [Vertex.b, Vertex.core]))
        rcases hadj with heq | hn
        · exact False.elim (cert.c_ne_i (Vertex.c0 cert) q heq.symm)
        · exact False.elim (hn ((cert.mem_T q).1 hqT))
      · obtain ⟨r, hrE, hrq, hrw⟩ := hx
        have hrK : Vertex.x cert (some r) ∈ K := by
          simpa [hrw] using hw
        have hadj :=
          (BlueGraph cert).adj_symm
            (hK.isClique hiq hrK (by simp [Vertex.core, Vertex.x]))
        have heq :=
          (blue_adj_xSome_core_iff cert r (cert.i q)).1 hadj
        exact False.elim (hrq (cert.i.injective heq).symm)
      · have hxK : Vertex.x cert none ∈ K := by
          simpa [hxstar] using hw
        exact False.elim <| not_blue_adj_xNone_core cert (cert.i q)
          ((BlueGraph cert).adj_symm
            (hK.isClique hiq hxK (by simp [Vertex.core, Vertex.x])))
      · exact Or.inr hy
      · obtain ⟨hq1, hrw⟩ := hz
        have hzK : Vertex.z ∈ K := by simpa [hrw] using hw
        rcases (blue_adj_z_core_iff cert (cert.i q)).1
            (hK.isClique hzK hiq (by simp [Vertex.core])) with heq | hn
        · exact False.elim (cert.c_ne_i (Vertex.c0 cert) q heq.symm)
        · exact False.elim (hn ((cert.mem_T q).1 hqT))
    by_cases hsmall :
        ∃ r : Fin (s - 1),
          Vertex.y cert (some r) ∈ K ∧ r.val < 2
    · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
      let Qsmall : Finset (Fin (s - 1)) :=
        {Certificates.i0Index' cert.five_le_s}
      have hr₀U : r₀ ∈ cert.U := by
        rcases hreduced _ hr₀K with hi | hy
        · simp at hi
        · obtain ⟨t, htU, heq⟩ := hy
          have htr : t = r₀ := (ySomeEmbedding cert).injective heq.symm
          simpa [htr] using htU
      have hYsmall (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) :
          r ∈ Qsmall := by
        have hrU : r ∈ cert.U := by
          rcases hreduced _ hrK with hi | hy
          · simp at hi
          · obtain ⟨t, htU, heq⟩ := hy
            have htr : t = r := (ySomeEmbedding cert).injective heq.symm
            simpa [htr] using htU
        have hrsmall : r.val < 2 := by
          by_cases hrr : r₀ = r
          · simpa [← hrr] using hr₀small
          · have hadj := hK.isClique hr₀K hrK (by
              intro heq
              exact hrr ((ySomeEmbedding cert).injective heq))
            rcases blue_adj_ySome_same_part_of_mem_U cert hG
                hr₀U hrU hadj with hs | hs
            · exact hs.2
            · omega
        have hre := caseB_U_small_eq_i0 cert hB hrU hrsmall
        simp [Qsmall, hre]
      have hsub :
          K ⊆ insert (Vertex.core (cert.i q))
            (xSet cert ∅ ∪ ySet cert Qsmall) := by
        intro w hw
        rcases hreduced w hw with hi | ⟨r, hrU, rfl⟩
        · simpa [hi]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_union_right _
              ((mem_ySet cert Qsmall r).2 (hYsmall r hw)))
      have hcard :=
        card_le_one_add_xSet_ySet
          (cert := cert) (K := K)
          (e := Vertex.core (cert.i q))
          (P := ∅) (Q := Qsmall) hsub
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hs := cert.five_le_s
      simp [Qsmall] at hcard
      omega
    · have hYlarge (r : Fin (s - 1))
          (hrK : Vertex.y cert (some r) ∈ K) :
          r ∈ cert.ULarge := by
        rcases hreduced _ hrK with hi | hy
        · simp at hi
        · obtain ⟨t, htU, heq⟩ := hy
          have htr : t = r := (ySomeEmbedding cert).injective heq.symm
          subst t
          exact (cert.mem_ULarge r).2 ⟨htU, by
            by_contra hr2
            exact hsmall ⟨r, hrK, by omega⟩⟩
      have hsub :
          K ⊆ insert (Vertex.core (cert.i q))
            (xSet cert ∅ ∪ ySet cert cert.ULarge) := by
        intro w hw
        rcases hreduced w hw with hi | ⟨r, hrU, rfl⟩
        · simpa [hi]
        · exact Finset.mem_insert_of_mem
            (Finset.mem_union_right _
              ((mem_ySet cert cert.ULarge r).2 (hYlarge r hw)))
      have hcard :=
        card_le_one_add_xSet_ySet
          (cert := cert) (K := K)
          (e := Vertex.core (cert.i q))
          (P := ∅) (Q := cert.ULarge) hsub
      have hUL := cert.caseB_card_ULarge_le hB
      have hcardK := hK.card_eq
      have hk := cert.five_le_k
      have hks := hB.k_le_s
      simp at hcard
      omega
  · by_cases hclone :
        (q = Vertex.i1 cert ∧
          Vertex.b (Vertex.c0 cert) ∈ K) ∨
        (q ≠ Vertex.i1 cert ∧ Vertex.z ∈ K)
    · rcases hclone with ⟨hq1, hb0⟩ | ⟨hq1, hzK⟩
      · have hreduced (w : Vertex V k s) (hw : w ∈ K) :
            w = Vertex.b (Vertex.c0 cert) ∨
              w = Vertex.x cert none ∨
              (∃ r : Fin (s - 1), r ∈ cert.U ∧
                w = Vertex.y cert (some r)) := by
          rcases hclass hw with hi | hb | hx | hxstar | hy | hz
          · exact False.elim (hiq (by simpa [hi] using hw))
          · exact Or.inl hb.2
          · obtain ⟨r, hrE, hrq, hrw⟩ := hx
            have hrK : Vertex.x cert (some r) ∈ K := by
              simpa [hrw] using hw
            have hadj :=
              (blue_adj_xSome_b_iff cert r (Vertex.c0 cert)).1
                ((BlueGraph cert).adj_symm
                  (hK.isClique hb0 hrK (by simp [Vertex.b, Vertex.x])))
            exact False.elim (hrq (hadj.1.trans hq1.symm))
          · exact Or.inr (Or.inl hxstar)
          · exact Or.inr (Or.inr hy)
          · exact False.elim (hz.1 hq1)
        by_cases hsmall :
            ∃ r : Fin (s - 1),
              Vertex.y cert (some r) ∈ K ∧ r.val < 2
        · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
          let Qsmall : Finset (Fin (s - 1)) :=
            {Certificates.i0Index' cert.five_le_s}
          have hr₀U : r₀ ∈ cert.U := by
            rcases hreduced _ hr₀K with hb | hx | hy
            · simp at hb
            · simp at hx
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r₀ := (ySomeEmbedding cert).injective heq.symm
              simpa [htr] using htU
          have hYsmall (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ Qsmall := by
            have hrU : r ∈ cert.U := by
              rcases hreduced _ hrK with hb | hx | hy
              · simp at hb
              · simp at hx
              · obtain ⟨t, htU, heq⟩ := hy
                have htr : t = r := (ySomeEmbedding cert).injective heq.symm
                simpa [htr] using htU
            have hrsmall : r.val < 2 := by
              by_cases hrr : r₀ = r
              · simpa [← hrr] using hr₀small
              · have hadj := hK.isClique hr₀K hrK (by
                  intro heq
                  exact hrr ((ySomeEmbedding cert).injective heq))
                rcases blue_adj_ySome_same_part_of_mem_U cert hG
                    hr₀U hrU hadj with hs | hs
                · exact hs.2
                · omega
            have hre := caseB_U_small_eq_i0 cert hB hrU hrsmall
            simp [Qsmall, hre]
          have hsub :
              K ⊆ insert (Vertex.b (Vertex.c0 cert))
                (insert (Vertex.x cert none)
                  (xSet cert ∅ ∪ ySet cert Qsmall)) := by
            intro w hw
            rcases hreduced w hw with hb | hx | ⟨r, hrU, rfl⟩
            · simpa [hb]
            · simpa [hx]
            · exact Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_union_right _
                    ((mem_ySet cert Qsmall r).2 (hYsmall r hw))))
          have hcard :=
            card_le_two_add_xSet_ySet
              (cert := cert) (K := K)
              (e₁ := Vertex.b (Vertex.c0 cert))
              (e₂ := Vertex.x cert none)
              (P := ∅) (Q := Qsmall) hsub
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hs := cert.five_le_s
          simp [Qsmall] at hcard
          omega
        · have hYlarge (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ cert.ULarge := by
            rcases hreduced _ hrK with hb | hx | hy
            · simp at hb
            · simp at hx
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r := (ySomeEmbedding cert).injective heq.symm
              subst t
              exact (cert.mem_ULarge r).2 ⟨htU, by
                by_contra hr2
                exact hsmall ⟨r, hrK, by omega⟩⟩
          have hsub :
              K ⊆ insert (Vertex.b (Vertex.c0 cert))
                (insert (Vertex.x cert none)
                  (xSet cert ∅ ∪ ySet cert cert.ULarge)) := by
            intro w hw
            rcases hreduced w hw with hb | hx | ⟨r, hrU, rfl⟩
            · simpa [hb]
            · simpa [hx]
            · exact Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem
                  (Finset.mem_union_right _
                    ((mem_ySet cert cert.ULarge r).2
                      (hYlarge r hw))))
          have hcard :=
            card_le_two_add_xSet_ySet
              (cert := cert) (K := K)
              (e₁ := Vertex.b (Vertex.c0 cert))
              (e₂ := Vertex.x cert none)
              (P := ∅) (Q := cert.ULarge) hsub
          have hUL := cert.caseB_card_ULarge_le hB
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          have hks := hB.k_le_s
          simp at hcard
          omega
      · have hq2 := caseB_E_ne_i1_large cert hB hqE hq1
        have hqEL : q ∈ cert.ELarge :=
          (cert.mem_ELarge q).2 ⟨hqE, hq2⟩
        let P := cert.ELarge.erase q
        have hPcard : P.card + 1 = cert.ELarge.card := by
          dsimp [P]
          have h := Finset.card_erase_of_mem hqEL
          have hpos := Finset.card_pos.mpr ⟨q, hqEL⟩
          omega
        have hreduced (w : Vertex V k s) (hw : w ∈ K) :
            w = Vertex.z ∨
              (∃ r : Fin (s - 1), r ∈ P ∧
                w = Vertex.x cert (some r)) ∨
              (∃ r : Fin (s - 1), r ∈ cert.U ∧
                w = Vertex.y cert (some r)) := by
          rcases hclass hw with hi | hb | hx | hxstar | hy | hz
          · exact False.elim (hiq (by simpa [hi] using hw))
          · exact False.elim (hq1 hb.1)
          · obtain ⟨r, hrE, hrq, hrw⟩ := hx
            have hrK : Vertex.x cert (some r) ∈ K := by
              simpa [hrw] using hw
            have hr1 := (blue_adj_z_xSome_iff cert r).1
              (hK.isClique hzK hrK (by simp [Vertex.x]))
            have hr2 := caseB_E_ne_i1_large cert hB hrE hr1
            exact Or.inr (Or.inl
              ⟨r, by
                rw [Finset.mem_erase]
                exact ⟨hrq, (cert.mem_ELarge r).2 ⟨hrE, hr2⟩⟩,
                hrw⟩)
          · have hxK : Vertex.x cert none ∈ K := by
              simpa [hxstar] using hw
            exact False.elim (not_blue_adj_z_xNone cert
              (hK.isClique hzK hxK (by simp [Vertex.x])))
          · exact Or.inr (Or.inr hy)
          · exact Or.inl hz.2
        by_cases hsmall :
            ∃ r : Fin (s - 1),
              Vertex.y cert (some r) ∈ K ∧ r.val < 2
        · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
          let Qsmall : Finset (Fin (s - 1)) :=
            {Certificates.i0Index' cert.five_le_s}
          have hr₀U : r₀ ∈ cert.U := by
            rcases hreduced _ hr₀K with hz | hx | hy
            · simp at hz
            · obtain ⟨_, _, hfalse⟩ := hx
              simp at hfalse
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r₀ := (ySomeEmbedding cert).injective heq.symm
              simpa [htr] using htU
          have hYsmall (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ Qsmall := by
            have hrU : r ∈ cert.U := by
              rcases hreduced _ hrK with hz | hx | hy
              · simp at hz
              · obtain ⟨_, _, hfalse⟩ := hx
                simp at hfalse
              · obtain ⟨t, htU, heq⟩ := hy
                have htr : t = r := (ySomeEmbedding cert).injective heq.symm
                simpa [htr] using htU
            have hrsmall : r.val < 2 := by
              by_cases hrr : r₀ = r
              · simpa [← hrr] using hr₀small
              · have hadj := hK.isClique hr₀K hrK (by
                  intro heq
                  exact hrr ((ySomeEmbedding cert).injective heq))
                rcases blue_adj_ySome_same_part_of_mem_U cert hG
                    hr₀U hrU hadj with hs | hs
                · exact hs.2
                · omega
            have hre := caseB_U_small_eq_i0 cert hB hrU hrsmall
            simp [Qsmall, hre]
          have hsub :
              K ⊆ insert Vertex.z
                (xSet cert P ∪ ySet cert Qsmall) := by
            intro w hw
            rcases hreduced w hw with hz | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
            · simpa [hz]
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_left _
                  ((mem_xSet cert P r).2 hrP))
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_right _
                  ((mem_ySet cert Qsmall r).2 (hYsmall r hw)))
          have hcard :=
            card_le_one_add_xSet_ySet
              (cert := cert) (K := K) (e := Vertex.z)
              (P := P) (Q := Qsmall) hsub
          have hEL := cert.caseB_card_ELarge_le hB
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          simp [Qsmall] at hcard
          omega
        · have hYlarge (r : Fin (s - 1))
              (hrK : Vertex.y cert (some r) ∈ K) :
              r ∈ cert.ULarge := by
            rcases hreduced _ hrK with hz | hx | hy
            · simp at hz
            · obtain ⟨_, _, hfalse⟩ := hx
              simp at hfalse
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r := (ySomeEmbedding cert).injective heq.symm
              subst t
              exact (cert.mem_ULarge r).2 ⟨htU, by
                by_contra hr2
                exact hsmall ⟨r, hrK, by omega⟩⟩
          have hsub :
              K ⊆ insert Vertex.z
                (xSet cert P ∪ ySet cert cert.ULarge) := by
            intro w hw
            rcases hreduced w hw with hz | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
            · simpa [hz]
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_left _
                  ((mem_xSet cert P r).2 hrP))
            · exact Finset.mem_insert_of_mem
                (Finset.mem_union_right _
                  ((mem_ySet cert cert.ULarge r).2 (hYlarge r hw)))
          have hcard :=
            card_le_one_add_xSet_ySet
              (cert := cert) (K := K) (e := Vertex.z)
              (P := P) (Q := cert.ULarge) hsub
          have hUL := cert.caseB_card_ULarge_le hB
          have hEL := cert.caseB_card_ELarge_le hB
          have hcardK := hK.card_eq
          have hk := cert.five_le_k
          omega
    · let P := cert.E.erase q
      have hPcard : P.card ≤ cert.ELarge.card := by
        dsimp [P]
        exact card_E_erase_le_ELarge cert hB hqE
      have hreduced (w : Vertex V k s) (hw : w ∈ K) :
          w = Vertex.x cert none ∨
            (∃ r : Fin (s - 1), r ∈ P ∧
              w = Vertex.x cert (some r)) ∨
            (∃ r : Fin (s - 1), r ∈ cert.U ∧
              w = Vertex.y cert (some r)) := by
        rcases hclass hw with hi | hb | hx | hxstar | hy | hz
        · exact False.elim (hiq (by simpa [hi] using hw))
        · have hbK : Vertex.b (Vertex.c0 cert) ∈ K := by
            simpa [hb.2] using hw
          exact False.elim (hclone (Or.inl ⟨hb.1, hbK⟩))
        · obtain ⟨r, hrE, hrq, hrw⟩ := hx
          exact Or.inr (Or.inl
            ⟨r, by simpa [P, hrq] using hrE, hrw⟩)
        · exact Or.inl hxstar
        · exact Or.inr (Or.inr hy)
        · have hzK : Vertex.z ∈ K := by simpa [hz.2] using hw
          exact False.elim (hclone (Or.inr ⟨hz.1, hzK⟩))
      by_cases hsmall :
          ∃ r : Fin (s - 1),
            Vertex.y cert (some r) ∈ K ∧ r.val < 2
      · obtain ⟨r₀, hr₀K, hr₀small⟩ := hsmall
        let Qsmall : Finset (Fin (s - 1)) :=
          {Certificates.i0Index' cert.five_le_s}
        have hr₀U : r₀ ∈ cert.U := by
          rcases hreduced _ hr₀K with hxstar | hx | hy
          · simp at hxstar
          · obtain ⟨_, _, hfalse⟩ := hx
            simp at hfalse
          · obtain ⟨t, htU, heq⟩ := hy
            have htr : t = r₀ := (ySomeEmbedding cert).injective heq.symm
            simpa [htr] using htU
        have hYsmall (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) :
            r ∈ Qsmall := by
          have hrU : r ∈ cert.U := by
            rcases hreduced _ hrK with hxstar | hx | hy
            · simp at hxstar
            · obtain ⟨_, _, hfalse⟩ := hx
              simp at hfalse
            · obtain ⟨t, htU, heq⟩ := hy
              have htr : t = r := (ySomeEmbedding cert).injective heq.symm
              simpa [htr] using htU
          have hrsmall : r.val < 2 := by
            by_cases hrr : r₀ = r
            · simpa [← hrr] using hr₀small
            · have hadj := hK.isClique hr₀K hrK (by
                intro heq
                exact hrr ((ySomeEmbedding cert).injective heq))
              rcases blue_adj_ySome_same_part_of_mem_U cert hG
                  hr₀U hrU hadj with hs | hs
              · exact hs.2
              · omega
          have hre := caseB_U_small_eq_i0 cert hB hrU hrsmall
          simp [Qsmall, hre]
        have hsub :
            K ⊆ insert (Vertex.x cert none)
              (xSet cert P ∪ ySet cert Qsmall) := by
          intro w hw
          rcases hreduced w hw with hxstar | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
          · simpa [hxstar]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _
                ((mem_xSet cert P r).2 hrP))
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                ((mem_ySet cert Qsmall r).2 (hYsmall r hw)))
        have hcard :=
          card_le_one_add_xSet_ySet
            (cert := cert) (K := K) (e := Vertex.x cert none)
            (P := P) (Q := Qsmall) hsub
        have hEL := cert.caseB_card_ELarge_le hB
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hks := hB.k_le_s
        simp [Qsmall] at hcard
        omega
      · have hYlarge (r : Fin (s - 1))
            (hrK : Vertex.y cert (some r) ∈ K) :
            r ∈ cert.ULarge := by
          rcases hreduced _ hrK with hxstar | hx | hy
          · simp at hxstar
          · obtain ⟨_, _, hfalse⟩ := hx
            simp at hfalse
          · obtain ⟨t, htU, heq⟩ := hy
            have htr : t = r := (ySomeEmbedding cert).injective heq.symm
            subst t
            exact (cert.mem_ULarge r).2 ⟨htU, by
              by_contra hr2
              exact hsmall ⟨r, hrK, by omega⟩⟩
        have hsub :
            K ⊆ insert (Vertex.x cert none)
              (xSet cert P ∪ ySet cert cert.ULarge) := by
          intro w hw
          rcases hreduced w hw with hxstar | ⟨r, hrP, rfl⟩ | ⟨r, hrU, rfl⟩
          · simpa [hxstar]
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _
                ((mem_xSet cert P r).2 hrP))
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                ((mem_ySet cert cert.ULarge r).2 (hYlarge r hw)))
        have hcard :=
          card_le_one_add_xSet_ySet
            (cert := cert) (K := K) (e := Vertex.x cert none)
            (P := P) (Q := cert.ULarge) hsub
        have hUL := cert.caseB_card_ULarge_le hB
        have hEL := cert.caseB_card_ELarge_le hB
        have hcardK := hK.card_eq
        have hk := cert.five_le_k
        have hks := hB.k_le_s
        omega
end Switching
end RamseyIncrement
