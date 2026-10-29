/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.ChangedEdges
import Mathlib.Tactic

/-!
# Blue safety for switching row B6

This module proves row (B6) without importing the other blue-row proofs.
Safety of row (B1) is supplied explicitly as a hypothesis.
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

private abbrev hs
    (cert : Certificates.OrderedCertificates G k s) : 1 ≤ s :=
  le_trans (by decide : 1 ≤ 5)
    (cert.five_le_s)

private noncomputable abbrev BlueGraph
    (cert : Certificates.OrderedCertificates G k s) :=
  (finalGraph cert)ᶜ

/-- The exact row-(B1) hypothesis needed to exclude `b₀` from a
putative row-(B6) common-neighborhood clique. -/
def B1RowSafety
    (cert : Certificates.OrderedCertificates G k s) : Prop :=
  ∀ q ∈ cert.T,
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)))
      (s - 1)

/-- The two possible second endpoints in row (B6). -/
def IsB6Endpoint
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) : Prop :=
  (r = none ∧ cert.E.Nonempty) ∨
    ∃ q ∈ cert.E, 2 ≤ q.val ∧ r = some q

private theorem IsB6Endpoint.e_nonempty
    {cert : Certificates.OrderedCertificates G k s}
    {r : Option (Fin (s - 1))}
    (hr : IsB6Endpoint cert r) :
    cert.E.Nonempty := by
  rcases hr with ⟨_, hE⟩ | ⟨q, hqE, _, _⟩
  · exact hE
  · exact ⟨q, hqE⟩

private theorem IsB6Endpoint.ne_i1
    {cert : Certificates.OrderedCertificates G k s}
    {r : Option (Fin (s - 1))}
    (hr : IsB6Endpoint cert r) :
    r ≠ some (Vertex.i1 cert) := by
  rcases hr with ⟨rfl, _⟩ | ⟨q, _, hq2, rfl⟩
  · simp
  · intro h
    have hv := congrArg Fin.val (Option.some.inj h)
    have hi1val : (Vertex.i1 cert).val = 1 := rfl
    rw [hi1val] at hv
    omega

private theorem IsB6Endpoint.removed_adj
    {cert : Certificates.OrderedCertificates G k s}
    {r : Option (Fin (s - 1))}
    (hr : IsB6Endpoint cert r) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert))) (Vertex.y cert r) := by
  rcases hr with ⟨rfl, hE⟩ | ⟨q, hqE, hq2, rfl⟩
  · exact (removedRedGraph_adj_y1_yStar_iff cert).2 hE
  · exact (removedRedGraph_adj_y1_y_iff cert q hq2).2 hqE

private theorem blue_of_removed_not_added
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (hrem : (removedRedGraph cert).Adj u v)
    (hadd : ¬(addedRedGraph cert).Adj u v) :
    (BlueGraph cert).Adj u v := by
  rw [SimpleGraph.compl_adj]
  refine ⟨hrem.ne, ?_⟩
  intro hfinal
  rcases (final_adj_iff cert u v).1 hfinal with hpre | hadd'
  · exact hpre.2 hrem
  · exact hadd hadd'

private theorem IsB6Endpoint.blue_adj
    {cert : Certificates.OrderedCertificates G k s}
    {r : Option (Fin (s - 1))}
    (hr : IsB6Endpoint cert r) :
    (BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert))) (Vertex.y cert r) := by
  apply blue_of_removed_not_added cert hr.removed_adj
  simp [addedRedGraph_adj_iff, SymmPair]

private theorem blue_adj_x_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (BlueGraph cert).Adj (Vertex.x cert r) (Vertex.y cert t) ↔
      r ≠ t := by
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.x, Vertex.y, redJoinedClone]

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

private theorem blue_adj_yStar_ySome_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (BlueGraph cert).Adj
        (Vertex.y cert none) (Vertex.y cert (some q)) ↔
      2 ≤ q.val ∨
        (q = Vertex.i1 cert ∧ cert.E.Nonempty) := by
  have hs5 := cert.five_le_s
  have hq1 : q = Vertex.i1 cert ↔ q.val = 1 := by
    constructor
    · intro h
      simpa [h]
    · intro h
      apply Fin.ext
      simpa using h
  simp [BlueGraph, finalGraph, preGraph, canonicalGraph, Canonical.graph,
    removedRedGraph, removedRedRel, addedRedGraph, addedRedRel,
    Vertex.y, SameBPart, redJoinedClone, hq1]
  constructor
  · intro h
    by_cases hq2 : 2 ≤ q.val
    · exact Or.inl hq2
    · have hqle : q.val ≤ 1 := by omega
      have hswitch := h (fun hs2 ↦ by omega) (fun _ ↦ hqle)
      exact Or.inr ⟨hswitch.2, hswitch.1⟩
  · intro h _ hsmall
    rcases h with hq2 | ⟨hq, hE⟩
    · have hqle := hsmall (by omega : 2 ≤ s - 1)
      omega
    · exact ⟨hE, hq⟩

private theorem secondCertificateAt_compl_adj
    (cert : Certificates.OrderedCertificates G k s)
    {r t : Option (Fin (s - 1))} (hrt : r ≠ t) :
    (specialLift G cert.c)ᶜ.Adj
      (Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r)
      (Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k t) := by
  cases r with
  | none =>
      cases t with
      | none => simp at hrt
      | some q =>
          simp only [Canonical.secondCertificateAt]
          rw [(specialLift G cert.c)ᶜ.adj_comm,
            specialLift_compl_adj_core_a]
          exact cert.c_ne_i (Vertex.c0 cert) q
  | some p =>
      cases t with
      | none =>
          simp only [Canonical.secondCertificateAt]
          rw [specialLift_compl_adj_core_a]
          exact cert.c_ne_i (Vertex.c0 cert) p
      | some q =>
          simp only [Canonical.secondCertificateAt]
          rw [specialLift_compl_adj_core_core]
          apply cert.i_compl_adj
          intro hpq
          apply hrt
          simpa [hpq]

private def xEmbedding
    (cert : Certificates.OrderedCertificates G k s) :
    Option (Fin (s - 1)) ↪ Vertex V k s where
  toFun r := Vertex.x cert r
  inj' := by
    intro r t h
    have houter :=
      SpecialLiftVertex.a.inj (Sum.inl.inj h)
    exact (Canonical.outerIndexEquiv
      (le_trans (by decide : 1 ≤ 5)
        (cert.five_le_s))).symm.injective houter

private def yEmbedding
    (cert : Certificates.OrderedCertificates G k s) :
    Option (Fin (s - 1)) ↪ Vertex V k s where
  toFun r := Vertex.y cert r
  inj' := by
    intro r t h
    have houter :=
      SpecialLiftVertex.b.inj (Sum.inl.inj h)
    exact (Canonical.outerIndexEquiv
      (le_trans (by decide : 1 ≤ 5)
        (cert.five_le_s))).symm.injective houter

private def someEmbedding (n : ℕ) : Fin n ↪ Option (Fin n) where
  toFun := some
  inj' _ _ h := Option.some.inj h

private noncomputable def b6W
    (cert : Certificates.OrderedCertificates G k s) :
    Finset (Option (Fin (s - 1))) :=
  insert none (cert.ELarge.map (someEmbedding (s - 1)))

@[simp]
private theorem mem_b6W_some
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    some q ∈ b6W cert ↔ q ∈ cert.ELarge := by
  simp only [b6W, Finset.mem_insert, Option.some_ne_none, false_or,
    Finset.mem_map]
  constructor
  · rintro ⟨r, hr, heq⟩
    have hrq : r = q := Option.some.inj heq
    simpa [hrq] using hr
  · intro hq
    exact ⟨q, hq, rfl⟩

@[simp]
private theorem mem_b6W_none
    (cert : Certificates.OrderedCertificates G k s) :
    none ∈ b6W cert := by
  simp [b6W]

private theorem eLarge_of_blue_y1_of_large
    (cert : Certificates.OrderedCertificates G k s)
    {q : Fin (s - 1)} (hq2 : 2 ≤ q.val)
    (hblue : (BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert (some q))) :
    q ∈ cert.ELarge := by
  rcases (blue_adj_ySome_ySome_iff cert (Vertex.i1 cert) q).1 hblue with
    ⟨_, hpart | hswitch | hswitch⟩
  · simp [Canonical.outerIndexEquiv, SameBPart] at hpart
    omega
  · exact (cert.mem_ELarge q).2
      ⟨hswitch.2.1, hq2⟩
  · have hq1 := congrArg Fin.val hswitch.1
    have hi1val : (Vertex.i1 cert).val = 1 := rfl
    rw [hi1val] at hq1
    omega

private theorem common_y_mem_b6W
    (cert : Certificates.OrderedCertificates G k s)
    {r : Option (Fin (s - 1))} (hr : IsB6Endpoint cert r)
    {t : Option (Fin (s - 1))}
    (h1 : (BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert))) (Vertex.y cert t))
    (hr' : (BlueGraph cert).Adj
      (Vertex.y cert r) (Vertex.y cert t)) :
    t ∈ b6W cert := by
  cases t with
  | none => exact mem_b6W_none cert
  | some q =>
      apply (mem_b6W_some cert q).2
      apply eLarge_of_blue_y1_of_large cert
      · rcases hr with ⟨rfl, _⟩ | ⟨p, _, hp2, rfl⟩
        · rcases (blue_adj_yStar_ySome_iff cert q).1 hr' with
            hq2 | ⟨hq1, _⟩
          · exact hq2
          · subst q
            exact False.elim ((BlueGraph cert).loopless.irrefl _ h1)
        ·
          have hp1 : p ≠ Vertex.i1 cert := by
            intro hp1
            have hv := congrArg Fin.val hp1
            have hi1val : (Vertex.i1 cert).val = 1 := rfl
            rw [hi1val] at hv
            omega
          have hq1 : q ≠ Vertex.i1 cert := by
            intro hq1
            subst q
            exact (BlueGraph cert).loopless.irrefl _ h1
          rcases (blue_adj_ySome_ySome_iff cert p q).1 hr' with
            ⟨_, hpart | hswitch | hswitch⟩
          · simp [Canonical.outerIndexEquiv, SameBPart] at hpart
            omega
          · exact False.elim (hp1 hswitch.1)
          · exact False.elim (hq1 hswitch.1)
      · exact h1

private theorem not_blue_y1_a0
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) (hE : cert.E.Nonempty) :
    ¬(BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.a (Vertex.c0 cert)) := by
  intro hblue
  have hi1E := (cert.E_nonempty_iff_i1_mem hG).1 hE
  have hi1T := cert.E_subset_T hi1E
  have hred :
      (finalGraph cert).Adj
        (Vertex.y cert (some (Vertex.i1 cert)))
        (Vertex.a (Vertex.c0 cert)) :=
    (final_adj_iff cert _ _).2
      (Or.inr ((addedRedGraph_adj_y_a0_iff cert _).2 hi1T))
  exact ((SimpleGraph.compl_adj _ _ _).1 hblue).2 hred

private theorem not_blue_y1_z
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) (hE : cert.E.Nonempty) :
    ¬(BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert))) Vertex.z := by
  intro hblue
  have hi1E := (cert.E_nonempty_iff_i1_mem hG).1 hE
  have hi1T := cert.E_subset_T hi1E
  have hb0y :
      (preGraph cert).Adj
        (Vertex.b (Vertex.c0 cert))
        (Vertex.y cert (some (Vertex.i1 cert))) :=
    (preGraph_adj_b0_y_iff cert _).2 hi1T
  have hzy :
      (preGraph cert).Adj Vertex.z
        (Vertex.y cert (some (Vertex.i1 cert))) := by
    change
      (redJoinedClone (canonicalGraph cert)
        (.core (.b (Vertex.c0 cert)))).Adj
        CloneVertex.z
        (.inl (.b ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            (cert.five_le_s))).symm
              (some (Vertex.i1 cert)))))
    rw [redJoinedClone.adj_z_old]
    right
    exact hb0y
  have hrem :
      ¬(removedRedGraph cert).Adj Vertex.z
        (Vertex.y cert (some (Vertex.i1 cert))) := by
    simp [removedRedGraph_adj_iff, SymmPair]
  have hred :
      (finalGraph cert).Adj Vertex.z
        (Vertex.y cert (some (Vertex.i1 cert))) :=
    (final_adj_iff cert _ _).2 (Or.inl ⟨hzy, hrem⟩)
  exact ((SimpleGraph.compl_adj _ _ _).1 hblue).2
    ((finalGraph cert).adj_symm hred)

private theorem blue_lower_lower_to_first
    (cert : Certificates.OrderedCertificates G k s)
    {d e : SpecialLiftVertex V k}
    (hblue : (BlueGraph cert).Adj
      (Vertex.lower d) (Vertex.lower e)) :
    (specialLift G cert.c)ᶜ.Adj d e := by
  have hsource :
      (preGraph cert)ᶜ.Adj (Vertex.lower d) (Vertex.lower e) := by
    by_contra h
    have hrem := classify_new_blue_edge cert hblue h
    simp [removedRedGraph_adj_iff, SymmPair] at hrem
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, ?_⟩
  · intro hde
    subst e
    exact (BlueGraph cert).loopless.irrefl _ hblue
  · intro hred
    exact ((SimpleGraph.compl_adj _ _ _).1 hsource).2
      ((preGraph_adj_lower_lower_iff cert d e).2 hred)

private theorem blue_lower_y_to_first
    (cert : Certificates.OrderedCertificates G k s)
    {d : SpecialLiftVertex V k} {r : Option (Fin (s - 1))}
    (hd0 : (Vertex.lower d : Vertex V k s) ≠
      Vertex.b (Vertex.c0 cert))
    (hblue : (BlueGraph cert).Adj
      (Vertex.lower d) (Vertex.y cert r)) :
    (specialLift G cert.c)ᶜ.Adj d
      (Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r) := by
  have hsource :
      (preGraph cert)ᶜ.Adj
        (Vertex.lower d) (Vertex.y cert r) := by
    by_contra h
    have hrem := classify_new_blue_edge cert hblue h
    simp [removedRedGraph_adj_iff, SymmPair] at hrem
    obtain ⟨q, _, hd, rfl⟩ := hrem
    apply hd0
    simpa [hd]
  have hnot :=
    ((SimpleGraph.compl_adj _ _ _).1 hsource).2
  rw [preGraph_adj_lower_y_iff] at hnot
  rw [SimpleGraph.compl_adj]
  constructor
  · intro heq
    exact hnot (Or.inl heq)
  · intro hadj
    exact hnot (Or.inr hadj.symm)

private theorem blue_x_lower_eq_second
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) (hE : cert.E.Nonempty)
    {r : Option (Fin (s - 1))} {d : SpecialLiftVertex V k}
    (hd0 : (Vertex.lower d : Vertex V k s) ≠
      Vertex.b (Vertex.c0 cert))
    (hy1 : (BlueGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert))) (Vertex.lower d))
    (hx : (BlueGraph cert).Adj
      (Vertex.x cert r) (Vertex.lower d)) :
    d = Canonical.secondCertificateAt cert.toCertificates
      cert.five_le_k r := by
  have hda0 :
      (Vertex.lower d : Vertex V k s) ≠
        Vertex.a (Vertex.c0 cert) := by
    intro hda0
    apply not_blue_y1_a0 cert hG hE
    simpa [hda0] using hy1
  have hsource :
      (preGraph cert)ᶜ.Adj
        (Vertex.x cert r) (Vertex.lower d) := by
    by_contra h
    have hrem := classify_new_blue_edge cert hx h
    simp [removedRedGraph_adj_iff, SymmPair, hd0, hda0] at hrem
  have hnot :=
    ((SimpleGraph.compl_adj _ _ _).1 hsource).2
  rw [(preGraph cert).adj_comm, preGraph_adj_lower_x_iff] at hnot
  exact (not_ne_iff.mp hnot).symm

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

private def b6Projection
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → SpecialLiftVertex V k
  | .inl (.core d) => d
  | .inl (.b r) =>
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
        (Canonical.outerIndexEquiv (hs cert) r)
  | _ => .a (Vertex.c0 cert)

@[simp]
private theorem b6Projection_lower
    (cert : Certificates.OrderedCertificates G k s)
    (d : SpecialLiftVertex V k) :
    b6Projection cert (Vertex.lower d : Vertex V k s) = d :=
  rfl

@[simp]
private theorem b6Projection_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    b6Projection cert (Vertex.y cert r) =
      Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r := by
  simp [b6Projection, Vertex.y]

private theorem b0_not_mem_of_b1
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB1 : B1RowSafety cert)
    {r : Option (Fin (s - 1))} (hr : IsB6Endpoint cert r)
    {K : Finset (Vertex V k s)}
    (hcommon : ∀ {w : Vertex V k s}, w ∈ K →
      (BlueGraph cert).Adj
          (Vertex.y cert (some (Vertex.i1 cert))) w ∧
        (BlueGraph cert).Adj (Vertex.y cert r) w)
    (hK : (BlueGraph cert).IsNClique (s - 1) K) :
    Vertex.b (Vertex.c0 cert) ∉ K := by
  classical
  intro hb0K
  rcases hr with ⟨rfl, hE⟩ | ⟨q, hqE, hq2, rfl⟩
  · have hred :
        (finalGraph cert).Adj
          (Vertex.y cert none) (Vertex.b (Vertex.c0 cert)) :=
      (final_adj_iff cert _ _).2
        (Or.inr (addedRedGraph_adj_yStar_b0 cert))
    exact ((SimpleGraph.compl_adj _ _ _).1 (hcommon hb0K).2).2 hred
  · have hE : cert.E.Nonempty := ⟨q, hqE⟩
    have hi1E := (cert.E_nonempty_iff_i1_mem hG).1 hE
    have hi1T := cert.E_subset_T hi1E
    have hqT := cert.E_subset_T hqE
    have hb0q :
        (BlueGraph cert).Adj
          (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)) := by
      apply blue_of_removed_not_added cert
      · exact (removedRedGraph_adj_b0_y_iff cert q).2 hqT
      · simp [addedRedGraph_adj_iff, SymmPair]
    have hqNotK : Vertex.y cert (some q) ∉ K := by
      intro hqK
      exact (BlueGraph cert).loopless.irrefl _ (hcommon hqK).2
    let K' :=
      insert (Vertex.y cert (some q))
        (K.erase (Vertex.b (Vertex.c0 cert)))
    have hK'Clique : (BlueGraph cert).IsClique (K' : Set _) := by
      have herase :
          (BlueGraph cert).IsClique
            (↑(K.erase (Vertex.b (Vertex.c0 cert))) : Set _) :=
        hK.isClique.subset (by
          intro w hw
          exact (Finset.mem_erase.mp hw).2)
      rw [Finset.coe_insert]
      exact herase.insert fun w hw _ ↦ by
        exact (hcommon (Finset.mem_of_mem_erase hw)).2
    have hK'Card : K'.card = s - 1 := by
      have hnot :
          Vertex.y cert (some q) ∉
            K.erase (Vertex.b (Vertex.c0 cert)) := by
        simp [hqNotK]
      dsimp [K']
      rw [Finset.card_insert_of_notMem hnot,
        Finset.card_erase_of_mem hb0K, hK.card_eq]
      have hs5 := cert.five_le_s
      omega
    have hK'Sub :
        (K' : Set (Vertex V k s)) ⊆
          (BlueGraph cert).commonNeighbors
            (Vertex.b (Vertex.c0 cert))
            (Vertex.y cert (some (Vertex.i1 cert))) := by
      intro w hw
      rw [(BlueGraph cert).mem_commonNeighbors]
      have hw' : w ∈ K' := hw
      simp only [K', Finset.mem_insert, Finset.mem_erase] at hw'
      rcases hw' with rfl | ⟨hw0, hwK⟩
      · exact ⟨hb0q,
          IsB6Endpoint.blue_adj (cert := cert)
            (r := some q) (Or.inr ⟨q, hqE, hq2, rfl⟩)⟩
      · exact ⟨hK.isClique hb0K hwK (by
          intro heq
          exact hw0 heq.symm), (hcommon hwK).1⟩
    exact hB1 (Vertex.i1 cert) hi1T hK'Sub
      ⟨hK'Clique, hK'Card⟩

private theorem b6_no_x_impossible
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {r : Option (Fin (s - 1))} (hr : IsB6Endpoint cert r)
    {K : Finset (Vertex V k s)}
    (hcommon : ∀ {w : Vertex V k s}, w ∈ K →
      (BlueGraph cert).Adj
          (Vertex.y cert (some (Vertex.i1 cert))) w ∧
        (BlueGraph cert).Adj (Vertex.y cert r) w)
    (hK : (BlueGraph cert).IsNClique (s - 1) K)
    (hb0 : Vertex.b (Vertex.c0 cert) ∉ K)
    (hnoX : ∀ t : Option (Fin (s - 1)), Vertex.x cert t ∉ K) :
    False := by
  classical
  let y1 := Vertex.y cert (some (Vertex.i1 cert))
  let yr := Vertex.y cert r
  let big := insert y1 (insert yr K)
  have h1r : y1 ≠ yr := by
    intro h
    exact hr.ne_i1 ((yEmbedding cert).injective h.symm)
  have h1NotK : y1 ∉ K := by
    intro h1K
    exact (BlueGraph cert).loopless.irrefl _ (hcommon h1K).1
  have hrNotK : yr ∉ K := by
    intro hrK
    exact (BlueGraph cert).loopless.irrefl _ (hcommon hrK).2
  have hbigClique : (BlueGraph cert).IsClique (big : Set _) := by
    have hinner :
        (BlueGraph cert).IsClique (↑(insert yr K) : Set _) := by
      rw [Finset.coe_insert]
      exact hK.isClique.insert fun w hw _ ↦ (hcommon hw).2
    rw [Finset.coe_insert]
    exact hinner.insert fun w hw _ ↦ by
      simp only [Finset.coe_insert, Set.mem_insert_iff,
        Finset.mem_coe] at hw
      rcases hw with rfl | hw
      · exact hr.blue_adj
      · exact (hcommon hw).1
  have hbigCard : big.card = s + 1 := by
    dsimp [big]
    rw [Finset.card_insert_of_notMem (by simp [h1r, h1NotK]),
      Finset.card_insert_of_notMem hrNotK, hK.card_eq]
    have hs5 := cert.five_le_s
    omega
  have hb0Big : Vertex.b (Vertex.c0 cert) ∉ big := by
    simp [big, y1, yr, hb0]
  have hallowed :
      ∀ {w : Vertex V k s}, w ∈ big →
        (∃ d : SpecialLiftVertex V k, w = Vertex.lower d) ∨
          ∃ t : Option (Fin (s - 1)), w = Vertex.y cert t := by
    intro w hw
    have hwCases := vertex_cases cert w
    rcases hwCases with hcore | ha | hb | hx | hy | hz
    · obtain ⟨v, rfl⟩ := hcore
      exact Or.inl ⟨.core v, rfl⟩
    · obtain ⟨p, rfl⟩ := ha
      exact Or.inl ⟨.a p, rfl⟩
    · obtain ⟨p, rfl⟩ := hb
      exact Or.inl ⟨.b p, rfl⟩
    · obtain ⟨t, rfl⟩ := hx
      have hxt : Vertex.x cert t ∉ big := by
        simp [big, y1, yr, hnoX t]
      exact False.elim (hxt hw)
    · exact Or.inr hy
    · subst w
      have hzNot : Vertex.z ∉ big := by
        intro hzBig
        have hadj := hbigClique
          (Finset.mem_insert_self _ _) hzBig (by simp [y1])
        exact not_blue_y1_z cert hG hr.e_nonempty hadj
      exact False.elim (hzNot hw)
  have hprojInj :
      Set.InjOn (b6Projection cert) (big : Set (Vertex V k s)) := by
    intro u hu v hv huv
    rcases hallowed hu with ⟨d, rfl⟩ | ⟨t, rfl⟩
    · rcases hallowed hv with ⟨e, rfl⟩ | ⟨z, rfl⟩
      · have hde : d = e := by simpa using huv
        subst e
        rfl
      · have hd0 :
            (Vertex.lower d : Vertex V k s) ≠
              Vertex.b (Vertex.c0 cert) := by
          intro hd
          apply hb0Big
          simpa [hd] using hu
        have hadj := hbigClique hu hv (by simp)
        have hfirst := blue_lower_y_to_first cert hd0 hadj
        have hEq : d =
            Canonical.secondCertificateAt cert.toCertificates
              cert.five_le_k z := by simpa using huv
        rw [hEq] at hfirst
        exact False.elim
          ((specialLift G cert.c)ᶜ.loopless.irrefl _ hfirst)
    · rcases hallowed hv with ⟨e, rfl⟩ | ⟨z, rfl⟩
      · have he0 :
            (Vertex.lower e : Vertex V k s) ≠
              Vertex.b (Vertex.c0 cert) := by
          intro he
          apply hb0Big
          simpa [he] using hv
        have hadj := (BlueGraph cert).adj_symm
          (hbigClique hu hv (by simp))
        have hfirst := blue_lower_y_to_first cert he0 hadj
        have hEq : e =
            Canonical.secondCertificateAt cert.toCertificates
              cert.five_le_k t := by simpa using huv.symm
        rw [hEq] at hfirst
        exact False.elim
          ((specialLift G cert.c)ᶜ.loopless.irrefl _ hfirst)
      · have htz : t = z :=
          Canonical.secondCertificateAt_injective
            cert.toCertificates cert.five_le_k (by simpa using huv)
        subst z
        rfl
  have hprojAdj :
      ∀ {u v : Vertex V k s}, u ∈ big → v ∈ big → u ≠ v →
        (specialLift G cert.c)ᶜ.Adj
          (b6Projection cert u) (b6Projection cert v) := by
    intro u v hu hv huv
    have hadj := hbigClique hu hv huv
    rcases hallowed hu with ⟨d, rfl⟩ | ⟨t, rfl⟩
    · rcases hallowed hv with ⟨e, rfl⟩ | ⟨z, rfl⟩
      · simpa only [b6Projection_lower] using
          (blue_lower_lower_to_first cert hadj)
      · have hd0 :
            (Vertex.lower d : Vertex V k s) ≠
              Vertex.b (Vertex.c0 cert) := by
          intro hd
          apply hb0Big
          simpa [hd] using hu
        simpa only [b6Projection_lower, b6Projection_y] using
          (blue_lower_y_to_first cert hd0 hadj)
    · rcases hallowed hv with ⟨e, rfl⟩ | ⟨z, rfl⟩
      · have he0 :
            (Vertex.lower e : Vertex V k s) ≠
              Vertex.b (Vertex.c0 cert) := by
          intro he
          apply hb0Big
          simpa [he] using hv
        simpa only [b6Projection_lower, b6Projection_y] using
          ((specialLift G cert.c)ᶜ.adj_symm
            (blue_lower_y_to_first cert he0
              ((BlueGraph cert).adj_symm hadj)))
      · simpa only [b6Projection_y] using
          (secondCertificateAt_compl_adj cert (by
            intro htz
            apply huv
            simpa [htz]))
  let f : {w // w ∈ big} ↪ SpecialLiftVertex V k :=
    { toFun := fun w ↦ b6Projection cert w.1
      inj' := by
        intro u v huv
        apply Subtype.ext
        exact hprojInj u.property v.property huv }
  have hfclique :
      ∀ u v : {w // w ∈ big}, u ≠ v →
        (specialLift G cert.c)ᶜ.Adj (f u) (f v) := by
    intro u v huv
    apply hprojAdj u.property v.property
    intro heq
    exact huv (Subtype.ext heq)
  have hfirstFree :
      IsRamseyFree (specialLift G cert.c) k (s + 1) :=
    specialLift_isRamseyFree G cert.c cert.c_isClique
      cert.five_le_k hG
  have hlt :=
    card_lt_of_cliqueFree_of_embedding hfirstFree.2 f hfclique
  have : big.card < s + 1 := by simpa using hlt
  omega

private theorem b6_with_x_impossible
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {r : Option (Fin (s - 1))} (hr : IsB6Endpoint cert r)
    {K : Finset (Vertex V k s)}
    (hcommon : ∀ {w : Vertex V k s}, w ∈ K →
      (BlueGraph cert).Adj
          (Vertex.y cert (some (Vertex.i1 cert))) w ∧
        (BlueGraph cert).Adj (Vertex.y cert r) w)
    (hK : (BlueGraph cert).IsNClique (s - 1) K)
    (hb0 : Vertex.b (Vertex.c0 cert) ∉ K)
    (hhasX : ∃ t : Option (Fin (s - 1)), Vertex.x cert t ∈ K) :
    False := by
  classical
  let P :=
    (Finset.univ : Finset (Option (Fin (s - 1)))).filter
      fun t ↦ Vertex.x cert t ∈ K
  let Q :=
    (Finset.univ : Finset (Option (Fin (s - 1)))).filter
      fun t ↦ Vertex.y cert t ∈ K
  let O :=
    K.filter fun w ↦
      (¬∃ t : Option (Fin (s - 1)), w = Vertex.x cert t) ∧
      (¬∃ t : Option (Fin (s - 1)), w = Vertex.y cert t)
  let PX := P.map (xEmbedding cert)
  let QY := Q.map (yEmbedding cert)
  have hmemP (t : Option (Fin (s - 1))) :
      t ∈ P ↔ Vertex.x cert t ∈ K := by
    simp [P]
  have hmemQ (t : Option (Fin (s - 1))) :
      t ∈ Q ↔ Vertex.y cert t ∈ K := by
    simp [Q]
  have hcover : K ⊆ (PX ∪ QY) ∪ O := by
    intro w hw
    by_cases hx : ∃ t : Option (Fin (s - 1)), w = Vertex.x cert t
    · obtain ⟨t, rfl⟩ := hx
      exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_map.2 ⟨t, (hmemP t).2 hw, rfl⟩))
    · by_cases hy : ∃ t : Option (Fin (s - 1)), w = Vertex.y cert t
      · obtain ⟨t, rfl⟩ := hy
        exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_map.2 ⟨t, (hmemQ t).2 hw, rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2
          ⟨hw, hx, hy⟩)
  have hKbound : K.card ≤ P.card + Q.card + O.card := by
    have h₀ := Finset.card_le_card hcover
    have h₁ := Finset.card_union_le (PX ∪ QY) O
    have h₂ := Finset.card_union_le PX QY
    have hPX : PX.card = P.card := by simp [PX]
    have hQY : QY.card = Q.card := by simp [QY]
    omega
  have hPne1 :
      ∀ {t}, t ∈ P → t ≠ some (Vertex.i1 cert) := by
    intro t ht
    have htK := (hmemP t).1 ht
    exact (blue_adj_x_y_iff cert t
      (some (Vertex.i1 cert))).1
        ((BlueGraph cert).adj_symm (hcommon htK).1)
  have hPner : ∀ {t}, t ∈ P → t ≠ r := by
    intro t ht
    have htK := (hmemP t).1 ht
    exact (blue_adj_x_y_iff cert t r).1
      ((BlueGraph cert).adj_symm (hcommon htK).2)
  have hQne1 :
      ∀ {t}, t ∈ Q → t ≠ some (Vertex.i1 cert) := by
    intro t ht ht1
    have htK := (hmemQ t).1 ht
    subst t
    exact (BlueGraph cert).loopless.irrefl _ (hcommon htK).1
  have hQner : ∀ {t}, t ∈ Q → t ≠ r := by
    intro t ht htr
    have htK := (hmemQ t).1 ht
    subst t
    exact (BlueGraph cert).loopless.irrefl _ (hcommon htK).2
  have hQW : ∀ {t}, t ∈ Q → t ∈ b6W cert := by
    intro t ht
    have htK := (hmemQ t).1 ht
    exact common_y_mem_b6W cert hr (hcommon htK).1 (hcommon htK).2
  have hPQdisjoint : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro t htP htQ
    have hxK := (hmemP t).1 htP
    have hyK := (hmemQ t).1 htQ
    have hxy := hK.isClique hxK hyK (by simp)
    exact (blue_adj_x_y_iff cert t t).1 hxy rfl
  have hPQsub :
      P ∪ Q ⊆
        ((Finset.univ.erase (some (Vertex.i1 cert))).erase r) := by
    intro t ht
    rcases Finset.mem_union.1 ht with htP | htQ
    · simp [hPne1 htP, hPner htP]
    · simp [hQne1 htQ, hQner htQ]
  have htargetCard :
      (((Finset.univ.erase (some (Vertex.i1 cert))).erase r) :
        Finset (Option (Fin (s - 1)))).card = s - 2 := by
    simp [hr.ne_i1]
    have hs5 := cert.five_le_s
    omega
  have hPQcard : P.card + Q.card ≤ s - 2 := by
    have hle := Finset.card_le_card hPQsub
    rw [Finset.card_union_of_disjoint hPQdisjoint,
      htargetCard] at hle
    exact hle
  have hrW : r ∈ b6W cert := by
    rcases hr with ⟨rfl, _⟩ | ⟨q, hqE, hq2, rfl⟩
    · exact mem_b6W_none cert
    · exact (mem_b6W_some cert q).2
        ((cert.mem_ELarge q).2 ⟨hqE, hq2⟩)
  have hWCard :
      (b6W cert).card = cert.ELarge.card + 1 := by
    have hnone :
        none ∉ cert.ELarge.map (someEmbedding (s - 1)) := by
      intro h
      obtain ⟨q, _, hq⟩ := Finset.mem_map.1 h
      simp [someEmbedding] at hq
    rw [b6W, Finset.card_insert_of_notMem hnone]
    simp
  have hWeraseCard :
      ((b6W cert).erase r).card = cert.ELarge.card := by
    rw [Finset.card_erase_of_mem hrW, hWCard]
    omega
  have hQsmall : Q.card ≤ cert.ELarge.card := by
    have hsub : Q ⊆ (b6W cert).erase r := by
      intro t ht
      exact Finset.mem_erase.2 ⟨hQner ht, hQW ht⟩
    have hle := Finset.card_le_card hsub
    rwa [hWeraseCard] at hle
  obtain ⟨hcaseB⟩ :=
    (cert.E_nonempty_iff_caseB hG).1 hr.e_nonempty
  have hEbound : cert.ELarge.card ≤ s - k :=
    cert.caseB_card_ELarge_le hcaseB
  have holdEq :
      ∀ {w : Vertex V k s} {t : Option (Fin (s - 1))},
        w ∈ O → t ∈ P →
          w = Vertex.lower
            (Canonical.secondCertificateAt cert.toCertificates
              cert.five_le_k t) := by
    intro w t hwO htP
    have hwData := Finset.mem_filter.1 hwO
    have hwK := hwData.1
    have htK := (hmemP t).1 htP
    have hclass := vertex_cases cert w
    rcases hclass with hcore | ha | hb | hx | hy | hz
    · obtain ⟨v, rfl⟩ := hcore
      have hd0 :
          (Vertex.lower (.core v) : Vertex V k s) ≠
            Vertex.b (Vertex.c0 cert) := by simp
      have hxt :=
        hK.isClique htK hwK (by simp)
      have heq := blue_x_lower_eq_second cert hG hr.e_nonempty
        hd0 (hcommon hwK).1 hxt
      simpa [heq]
    · obtain ⟨p, rfl⟩ := ha
      have hd0 :
          (Vertex.lower (.a p) : Vertex V k s) ≠
            Vertex.b (Vertex.c0 cert) := by simp
      have hxt :=
        hK.isClique htK hwK (by simp)
      have heq := blue_x_lower_eq_second cert hG hr.e_nonempty
        hd0 (hcommon hwK).1 hxt
      simpa [heq]
    · obtain ⟨p, rfl⟩ := hb
      have hp0 : p ≠ Vertex.c0 cert := by
        intro hp0
        subst p
        exact hb0 hwK
      have hd0 :
          (Vertex.lower (.b p) : Vertex V k s) ≠
            Vertex.b (Vertex.c0 cert) := by
        simpa using hp0
      have hxt :=
        hK.isClique htK hwK (by simp)
      have heq := blue_x_lower_eq_second cert hG hr.e_nonempty
        hd0 (hcommon hwK).1 hxt
      simpa [heq]
    · obtain ⟨z, hz⟩ := hx
      exact False.elim (hwData.2.1 ⟨z, hz⟩)
    · obtain ⟨z, hz⟩ := hy
      exact False.elim (hwData.2.2 ⟨z, hz⟩)
    · subst w
      exact False.elim
        (not_blue_y1_z cert hG hr.e_nonempty (hcommon hwK).1)
  obtain ⟨p, hpK⟩ := hhasX
  have hpP : p ∈ P := (hmemP p).2 hpK
  by_cases hPone : P.card = 1
  · have hOone : O.card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro u v hu hv
      rw [holdEq hu hpP, holdEq hv hpP]
    have hKcard := hK.card_eq
    have hQbound : Q.card ≤ s - k :=
      le_trans hQsmall hEbound
    have hk := cert.five_le_k
    have hs5 := cert.five_le_s
    omega
  · have hPtwo : 2 ≤ P.card := by
      have hPpos : 0 < P.card := Finset.card_pos.mpr ⟨p, hpP⟩
      omega
    obtain ⟨p₀, hp₀P, p₁, hp₁P, hpne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < P.card)
    have hOzero : O.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.2
      intro w hw
      have h0 := holdEq hw hp₀P
      have h1 := holdEq hw hp₁P
      rw [h0] at h1
      have hj :
          Canonical.secondCertificateAt cert.toCertificates
              cert.five_le_k p₀ =
            Canonical.secondCertificateAt cert.toCertificates
              cert.five_le_k p₁ := by
        simpa using h1
      exact hpne
        (Canonical.secondCertificateAt_injective
          cert.toCertificates cert.five_le_k hj)
    have hKcard := hK.card_eq
    omega

/-- Unified row-(B6) safety theorem for either listed second endpoint. -/
theorem blue_case_b6_of_b1
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB1 : B1RowSafety cert)
    {r : Option (Fin (s - 1))} (hr : IsB6Endpoint cert r) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.y cert (some (Vertex.i1 cert)))
        (Vertex.y cert r))
      (s - 1) := by
  classical
  intro K hKsub hK
  have hcommon {w : Vertex V k s} (hw : w ∈ K) :
      (BlueGraph cert).Adj
          (Vertex.y cert (some (Vertex.i1 cert))) w ∧
        (BlueGraph cert).Adj (Vertex.y cert r) w :=
    (BlueGraph cert).mem_commonNeighbors.1 (hKsub hw)
  have hb0 :=
    b0_not_mem_of_b1 cert hG hB1 hr hcommon hK
  by_cases hhasX :
      ∃ t : Option (Fin (s - 1)), Vertex.x cert t ∈ K
  · exact b6_with_x_impossible cert hG hr hcommon hK hb0 hhasX
  · apply b6_no_x_impossible cert hG hr hcommon hK hb0
    intro t ht
    exact hhasX ⟨t, ht⟩

/-- Row (B6), star endpoint: `y₁y_*` is blue-safe whenever `E` is
nonempty, assuming row (B1). -/
theorem blue_case_b6_star_of_b1
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB1 : B1RowSafety cert)
    (hE : cert.E.Nonempty) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.y cert (some (Vertex.i1 cert)))
        (Vertex.y cert none))
      (s - 1) :=
  blue_case_b6_of_b1 cert hG hB1 (Or.inl ⟨rfl, hE⟩)

/-- Row (B6), large exceptional endpoint: `y₁y_q` is blue-safe for
`q ∈ E`, `q ≥ 2`, assuming row (B1). -/
theorem blue_case_b6_large_of_b1
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB1 : B1RowSafety cert)
    {q : Fin (s - 1)} (hqE : q ∈ cert.E) (hq2 : 2 ≤ q.val) :
    (BlueGraph cert).CliqueFreeOn
      ((BlueGraph cert).commonNeighbors
        (Vertex.y cert (some (Vertex.i1 cert)))
        (Vertex.y cert (some q)))
      (s - 1) :=
  blue_case_b6_of_b1 cert hG hB1
    (Or.inr ⟨q, hqE, hq2, rfl⟩)

end Switching
end RamseyIncrement
