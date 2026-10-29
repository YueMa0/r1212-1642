/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Certificates
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod

/-!
# Strengthened certificate orientation

This file formalizes the strengthened orientation lemma used by the
second-connector argument.  Starting with any disjoint red and blue
certificate pair, it constructs one of four usable orientations: primal or
dual, and Type A or Type B.  Parameter order is derived locally in Type B;
Type A needs only the separate lower bounds on the two parameters.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

namespace Certificates

/-- General membership transport for `beta` under relabeling. -/
@[simp]
theorem relabel_mem_beta (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1)))
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    p ∈ (cert.relabel ec ei).beta q ↔ ec p ∈ cert.beta (ei q) := by
  simp only [mem_beta, relabel_c, relabel_i]

/-- Strengthened Type A: besides ordinary Type A, `c₁i₀` is red and
`c₂i₀` is blue. -/
def IsPlusCaseA (cert : Certificates G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s) : Prop :=
  cert.IsCaseA hk hs ∧
    G.Adj (cert.c (c1Index hk)) (cert.i (i0Index' hs)) ∧
    ¬G.Adj (cert.c (c2Index hk)) (cert.i (i0Index' hs))

/-- The complete data needed by the strengthened Type A construction. -/
structure PlusCaseAData (G : SimpleGraph V) (k s : ℕ) where
  cert : OrderedCertificates G k s
  isPlusA :
    cert.toCertificates.IsPlusCaseA cert.five_le_k cert.five_le_s

/-- The complete data needed by the strengthened Type B construction. -/
structure PlusCaseBData (G : SimpleGraph V) (k s : ℕ) where
  cert : OrderedCertificates G k s
  baseB : CaseBData cert.toCertificates cert.five_le_k

namespace PlusCaseAData

theorem caseA (data : PlusCaseAData G k s) :
    data.cert.toCertificates.IsCaseA
      data.cert.five_le_k data.cert.five_le_s :=
  data.isPlusA.1

theorem c1_not_unique (data : PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    ¬data.cert.IsUniqueBlueWitness
      (c1Index data.cert.five_le_k) q :=
  data.caseA.1 q

theorem c0_i0_red (data : PlusCaseAData G k s) :
    G.Adj
      (data.cert.c (c0Index data.cert.five_le_k))
      (data.cert.i (i0Index' data.cert.five_le_s)) :=
  data.caseA.2

theorem c1_i0_red (data : PlusCaseAData G k s) :
    G.Adj
      (data.cert.c (c1Index data.cert.five_le_k))
      (data.cert.i (i0Index' data.cert.five_le_s)) :=
  data.isPlusA.2.1

theorem c2_i0_blue (data : PlusCaseAData G k s) :
    ¬G.Adj
      (data.cert.c (c2Index data.cert.five_le_k))
      (data.cert.i (i0Index' data.cert.five_le_s)) :=
  data.isPlusA.2.2

end PlusCaseAData

namespace PlusCaseBData

theorem k_le_s (data : PlusCaseBData G k s) : k ≤ s :=
  data.baseB.k_le_s

theorem witnesses (data : PlusCaseBData G k s) :
    data.cert.IsCaseB data.cert.five_le_k data.baseB.k_le_s :=
  data.baseB.witnesses

end PlusCaseBData

/-- Interchange colors and the two certificate blocks. -/
def dual (cert : Certificates G k s) : Certificates Gᶜ s k where
  c := cert.i
  i := cert.c
  c_isClique := cert.i_isClique
  i_isClique := by simpa only [compl_compl] using cert.c_isClique
  disjoint := cert.disjoint.symm

@[simp]
theorem dual_c (cert : Certificates G k s) (q : Fin (s - 1)) :
    cert.dual.c q = cert.i q :=
  rfl

@[simp]
theorem dual_i (cert : Certificates G k s) (p : Fin (k - 1)) :
    cert.dual.i p = cert.c p :=
  rfl

@[simp]
theorem dual_dual_c (cert : Certificates G k s) (p : Fin (k - 1)) :
    cert.dual.dual.c p = cert.c p :=
  rfl

@[simp]
theorem dual_dual_i (cert : Certificates G k s) (q : Fin (s - 1)) :
    cert.dual.dual.i q = cert.i q :=
  rfl

/-- A blue incidence in the dual orientation is a red incidence in the
original orientation.  Disjointness supplies the required off-diagonal
fact for graph complementation. -/
@[simp]
theorem mem_dual_beta (cert : Certificates G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    q ∈ cert.dual.beta p ↔ G.Adj (cert.c p) (cert.i q) := by
  classical
  rw [mem_beta]
  simp only [dual_c, dual_i, compl_adj]
  have hne : cert.i q ≠ cert.c p := (cert.c_ne_i p q).symm
  constructor
  · intro h
    by_contra hadj
    exact h ⟨hne, by simpa [G.adj_comm] using hadj⟩
  · intro hadj hcompl
    exact hcompl.2 (by simpa [G.adj_comm] using hadj)

/-- The four possible outputs of the strengthened orientation lemma. -/
inductive PlusOrientation (G : SimpleGraph V) (k s : ℕ) : Type u
  | primalA (data : PlusCaseAData G k s)
  | primalB (data : PlusCaseBData G k s)
  | dualA (data : PlusCaseAData Gᶜ s k)
  | dualB (data : PlusCaseBData Gᶜ s k)

/-- The precise residual pattern after neither Type A nor Type B can be
obtained in a fixed orientation. -/
structure OrientationFailure (cert : Certificates G k s) : Prop where
  noUnique :
    ∀ (p : Fin (k - 1)) (q : Fin (s - 1)),
      ¬cert.IsUniqueBlueWitness p q
  redColumnSubsingleton :
    ∀ (q : Fin (s - 1)) (p r : Fin (k - 1)),
      G.Adj (cert.c p) (cert.i q) →
      G.Adj (cert.c r) (cert.i q) → p = r

private def firstThreeEmbedding (hk : 5 ≤ k) : Fin 3 ↪ Fin (k - 1) where
  toFun p := ⟨p.val, by omega⟩
  inj' p q h := by
    apply Fin.ext
    simpa using congrArg Fin.val h

/-- Extend a prescribed ordered triple of distinct row indices to a
permutation of all row indices. -/
private theorem exists_perm_map_three (hk : 5 ≤ k)
    (u0 u1 u2 : Fin (k - 1))
    (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h12 : u1 ≠ u2) :
    ∃ ec : Equiv.Perm (Fin (k - 1)),
      ec (c0Index hk) = u0 ∧
      ec (c1Index hk) = u1 ∧
      ec (c2Index hk) = u2 := by
  let target : Fin 3 → Fin (k - 1) := ![u0, u1, u2]
  have htarget : Function.Injective target := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [target]
  obtain ⟨ec, hec⟩ := Equiv.Perm.exists_extending_pair
    (firstThreeEmbedding hk) target
    (firstThreeEmbedding hk).injective htarget
  refine ⟨ec, ?_, ?_, ?_⟩
  · simpa [firstThreeEmbedding, c0Index, indexZero, target] using
      hec (0 : Fin 3)
  · simpa [firstThreeEmbedding, c1Index, indexOne, target] using
      hec (1 : Fin 3)
  · simpa [firstThreeEmbedding, c2Index, target] using
      hec (2 : Fin 3)

/-- A unique column together with an uncovered row relabels to strengthened
Type A. -/
theorem relabel_plusA_of_unique_and_uncovered
    (cert : Certificates G k s) (hk : 5 ≤ k) (hs : 5 ≤ s)
    {owner uncovered : Fin (k - 1)} {q0 : Fin (s - 1)}
    (hunique : cert.IsUniqueBlueWitness owner q0)
    (huncovered :
      ∀ q : Fin (s - 1), ¬cert.IsUniqueBlueWitness uncovered q) :
    Nonempty (PlusCaseAData G k s) := by
  classical
  have huo : uncovered ≠ owner := by
    intro h
    subst owner
    exact huncovered q0 hunique
  obtain ⟨other, hou, hoo⟩ :=
    Fin.exists_ne_and_ne_of_two_lt uncovered owner (by omega)
  obtain ⟨ec, hec0, hec1, hec2⟩ :=
    exists_perm_map_three hk other uncovered owner hou hoo huo
  let ei : Equiv.Perm (Fin (s - 1)) := Equiv.swap (i0Index' hs) q0
  have hei0 : ei (i0Index' hs) = q0 := by simp [ei]
  have hotherRed : G.Adj (cert.c other) (cert.i q0) := by
    by_contra hred
    have hm := (cert.mem_beta other q0).2 hred
    rw [hunique] at hm
    exact hoo (by simpa using hm)
  have huncoveredRed : G.Adj (cert.c uncovered) (cert.i q0) := by
    by_contra hred
    have hm := (cert.mem_beta uncovered q0).2 hred
    rw [hunique] at hm
    exact huo (by simpa using hm)
  have hownerBlue : ¬G.Adj (cert.c owner) (cert.i q0) :=
    (cert.mem_beta owner q0).1 (by rw [hunique]; simp)
  let finalCert := cert.relabel ec ei
  have hfinalA : finalCert.IsCaseA hk hs := by
    constructor
    · intro q hq
      have hold :
          cert.beta (ei q) = {ec (c1Index hk)} :=
        (cert.relabel_unique_iff ec ei (c1Index hk) q).1 hq
      exact huncovered (ei q) (by simpa [hec1] using hold)
    · simpa [finalCert, hec0, hei0] using hotherRed
  have hfinalPlus : finalCert.IsPlusCaseA hk hs := by
    refine ⟨hfinalA, ?_, ?_⟩
    · simpa [finalCert, hec1, hei0] using huncoveredRed
    · simpa [finalCert, hec2, hei0] using hownerBlue
  let ordered : OrderedCertificates G k s :=
    { finalCert with
      five_le_k := hk
      five_le_s := hs
      normal := .caseA hfinalA }
  refine ⟨{ cert := ordered, isPlusA := ?_ }⟩
  simpa [ordered] using hfinalPlus

/-- If every row owns a singleton column, choose distinct witnesses,
derive the oriented parameter inequality, and relabel to Type B. -/
theorem relabel_plusB_of_all_rows_owned
    (cert : Certificates G k s) (hk : 5 ≤ k) (hs : 5 ≤ s)
    (howned :
      ∀ p : Fin (k - 1),
        ∃ q : Fin (s - 1), cert.IsUniqueBlueWitness p q) :
    Nonempty (PlusCaseBData G k s) := by
  classical
  let witness : Fin (k - 1) → Fin (s - 1) :=
    fun p ↦ Classical.choose (howned p)
  have hwitness (p : Fin (k - 1)) :
      cert.IsUniqueBlueWitness p (witness p) :=
    Classical.choose_spec (howned p)
  have hwitness_inj : Function.Injective witness := by
    intro p r hpr
    have hsingle : ({p} : Finset (Fin (k - 1))) = {r} := by
      rw [← hwitness p, hpr, hwitness r]
    simpa using hsingle
  have hcard : k - 1 ≤ s - 1 := by
    simpa using Fintype.card_le_of_injective witness hwitness_inj
  have hks : k ≤ s := by omega
  obtain ⟨ei, hei⟩ := Equiv.Perm.exists_extending_pair
    (castIndex hks) witness (castIndex hks).injective hwitness_inj
  let finalCert := cert.relabel (Equiv.refl _) ei
  have hfinalB : finalCert.IsCaseB hk hks := by
    intro p
    apply (cert.relabel_unique_iff
      (Equiv.refl _) ei p (castIndex hks p)).2
    simpa [hei p] using hwitness p
  let baseB : CaseBData finalCert hk := ⟨hks, hfinalB⟩
  let ordered : OrderedCertificates G k s :=
    { finalCert with
      five_le_k := hk
      five_le_s := hs
      normal := .caseB baseB }
  refine ⟨{ cert := ordered, baseB := ?_ }⟩
  simpa [ordered] using baseB

/-- A column with two red rows and no singleton columns relabels to
strengthened Type A. -/
theorem relabel_plusA_of_mixed_column
    (cert : Certificates G k s) (hG : IsRamseyFree G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s)
    (hnoUnique :
      ∀ (p : Fin (k - 1)) (q : Fin (s - 1)),
        ¬cert.IsUniqueBlueWitness p q)
    {q0 : Fin (s - 1)} {p0 p1 : Fin (k - 1)}
    (hp01 : p0 ≠ p1)
    (hp0Red : G.Adj (cert.c p0) (cert.i q0))
    (hp1Red : G.Adj (cert.c p1) (cert.i q0)) :
    Nonempty (PlusCaseAData G k s) := by
  classical
  obtain ⟨p2, hp2mem⟩ :=
    cert.beta_nonempty hG (le_trans (by decide : 2 ≤ 5) hk) q0
  have hp2Blue : ¬G.Adj (cert.c p2) (cert.i q0) :=
    (cert.mem_beta p2 q0).1 hp2mem
  have hp02 : p0 ≠ p2 := by
    intro h
    subst p2
    exact hp2Blue hp0Red
  have hp12 : p1 ≠ p2 := by
    intro h
    subst p2
    exact hp2Blue hp1Red
  obtain ⟨ec, hec0, hec1, hec2⟩ :=
    exists_perm_map_three hk p0 p1 p2 hp01 hp02 hp12
  let ei : Equiv.Perm (Fin (s - 1)) := Equiv.swap (i0Index' hs) q0
  have hei0 : ei (i0Index' hs) = q0 := by simp [ei]
  let finalCert := cert.relabel ec ei
  have hfinalA : finalCert.IsCaseA hk hs := by
    constructor
    · intro q hq
      have hold :
          cert.beta (ei q) = {ec (c1Index hk)} :=
        (cert.relabel_unique_iff ec ei (c1Index hk) q).1 hq
      exact hnoUnique (ec (c1Index hk)) (ei q) hold
    · simpa [finalCert, hec0, hei0] using hp0Red
  have hfinalPlus : finalCert.IsPlusCaseA hk hs := by
    refine ⟨hfinalA, ?_, ?_⟩
    · simpa [finalCert, hec1, hei0] using hp1Red
    · simpa [finalCert, hec2, hei0] using hp2Blue
  let ordered : OrderedCertificates G k s :=
    { finalCert with
      five_le_k := hk
      five_le_s := hs
      normal := .caseA hfinalA }
  refine ⟨{ cert := ordered, isPlusA := ?_ }⟩
  simpa [ordered] using hfinalPlus

/-- In a fixed orientation, either one of the two strengthened normal forms
is available or the incidence matrix has the residual failure pattern. -/
theorem exists_plus_normal_form_or_failure
    (cert : Certificates G k s) (hG : IsRamseyFree G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s) :
    Nonempty (PlusCaseAData G k s) ∨
      Nonempty (PlusCaseBData G k s) ∨
      OrientationFailure cert := by
  classical
  by_cases howned :
      ∀ p : Fin (k - 1),
        ∃ q : Fin (s - 1), cert.IsUniqueBlueWitness p q
  · exact Or.inr (Or.inl
      (relabel_plusB_of_all_rows_owned cert hk hs howned))
  · have huncovered :
        ∃ p : Fin (k - 1),
          ∀ q : Fin (s - 1), ¬cert.IsUniqueBlueWitness p q := by
      push Not at howned
      exact howned
    obtain ⟨uncovered, huncovered⟩ := huncovered
    by_cases hanyUnique :
        ∃ owner : Fin (k - 1), ∃ q : Fin (s - 1),
          cert.IsUniqueBlueWitness owner q
    · obtain ⟨owner, q, hq⟩ := hanyUnique
      exact Or.inl
        (relabel_plusA_of_unique_and_uncovered
          cert hk hs hq huncovered)
    · have hnoUnique :
          ∀ (p : Fin (k - 1)) (q : Fin (s - 1)),
            ¬cert.IsUniqueBlueWitness p q := by
        push Not at hanyUnique
        exact hanyUnique
      by_cases hredSmall :
          ∀ (q : Fin (s - 1)) (p r : Fin (k - 1)),
            G.Adj (cert.c p) (cert.i q) →
            G.Adj (cert.c r) (cert.i q) → p = r
      · exact Or.inr (Or.inr ⟨hnoUnique, hredSmall⟩)
      · push Not at hredSmall
        obtain ⟨q, p, r, hp, hr, hpr⟩ := hredSmall
        exact Or.inl
          (relabel_plusA_of_mixed_column
            cert hG hk hs hnoUnique hpr hp hr)

/-- The finite set of blue incidences between the two certificate blocks.
It is the single set counted by columns and by rows in the contradiction
argument. -/
noncomputable def blueIncidencePairs
    (cert : Certificates G k s) :
    Finset (Fin (k - 1) × Fin (s - 1)) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter
    fun e ↦ e.1 ∈ cert.beta e.2

@[simp]
theorem mem_blueIncidencePairs
    (cert : Certificates G k s)
    (e : Fin (k - 1) × Fin (s - 1)) :
    e ∈ cert.blueIncidencePairs ↔ e.1 ∈ cert.beta e.2 := by
  classical
  simp [blueIncidencePairs]

/-- If the residual pattern occurs in both orientations, counting the same
blue incidence pairs by columns and rows contradicts `k ≤ s`. -/
theorem orientation_counting_contradiction
    (cert : Certificates G k s) (hG : IsRamseyFree G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s) (hks : k ≤ s)
    (hprimal : OrientationFailure cert)
    (hdual : OrientationFailure cert.dual) : False := by
  classical
  have htwo :
      ∀ q : Fin (s - 1),
        ∃ p ∈ cert.beta q, ∃ r ∈ cert.beta q, p ≠ r := by
    intro q
    have hnonempty :=
      cert.beta_nonempty hG (le_trans (by decide : 2 ≤ 5) hk) q
    have hcardPos : 0 < (cert.beta q).card :=
      Finset.card_pos.2 hnonempty
    have hcardNe : (cert.beta q).card ≠ 1 := by
      intro hcard
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
      exact hprimal.noUnique p q hp
    have hcard : 1 < (cert.beta q).card := by omega
    exact Finset.one_lt_card.mp hcard
  choose p0 hp0 p1 hp1 hp01 using htwo
  let pick : ∀ q : Fin (s - 1), Fin 2 → Fin (k - 1) :=
    fun q ↦ ![p0 q, p1 q]
  have pick_mem (q : Fin (s - 1)) (j : Fin 2) :
      pick q j ∈ cert.beta q := by
    fin_cases j
    · exact hp0 q
    · exact hp1 q
  have pick_inj (q : Fin (s - 1)) : Function.Injective (pick q) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      exact hp01 q (by simpa [pick] using hab)
    · exfalso
      exact hp01 q (by simpa [pick] using hab.symm)
    · rfl
  let Incidence :=
    {e : Fin (k - 1) × Fin (s - 1) //
      e ∈ cert.blueIncidencePairs}
  let lower : Fin (s - 1) × Fin 2 → Incidence :=
    fun e ↦ ⟨(pick e.1 e.2, e.1),
      (cert.mem_blueIncidencePairs _).2 (pick_mem e.1 e.2)⟩
  have hlowerInj : Function.Injective lower := by
    rintro ⟨q, a⟩ ⟨r, b⟩ h
    have hpair :
        (pick q a, q) = (pick r b, r) :=
      congrArg Subtype.val h
    have hqr : q = r := congrArg Prod.snd hpair
    subst r
    have hab : pick q a = pick q b :=
      congrArg Prod.fst hpair
    have : a = b := pick_inj q hab
    subst b
    rfl
  have blue_to_dual_red
      (p : Fin (k - 1)) (q : Fin (s - 1))
      (hpq : p ∈ cert.beta q) :
      Gᶜ.Adj (cert.i q) (cert.c p) := by
    rw [compl_adj]
    refine ⟨(cert.c_ne_i p q).symm, ?_⟩
    simpa [G.adj_comm] using (cert.mem_beta p q).1 hpq
  let upper : Incidence → Fin (k - 1) :=
    fun e ↦ e.1.1
  have hupperInj : Function.Injective upper := by
    intro x y hrow
    change x.1.1 = y.1.1 at hrow
    have hxblue : x.1.1 ∈ cert.beta x.1.2 :=
      (cert.mem_blueIncidencePairs x.1).1 x.2
    have hyblue : y.1.1 ∈ cert.beta y.1.2 :=
      (cert.mem_blueIncidencePairs y.1).1 y.2
    have hyblue' : x.1.1 ∈ cert.beta y.1.2 := by
      rw [hrow]
      exact hyblue
    have hcol : x.1.2 = y.1.2 :=
      hdual.redColumnSubsingleton x.1.1 x.1.2 y.1.2
        (blue_to_dual_red x.1.1 x.1.2 hxblue)
        (blue_to_dual_red x.1.1 y.1.2 hyblue')
    apply Subtype.ext
    apply Prod.ext
    · exact hrow
    · exact hcol
  have hlowerCard :=
    Fintype.card_le_of_injective lower hlowerInj
  have hupperCard :=
    Fintype.card_le_of_injective upper hupperInj
  simp only [Fintype.card_prod, Fintype.card_fin] at hlowerCard
  simp only [Fintype.card_fin] at hupperCard
  omega

/-- **Strengthened orientation lemma.** Every disjoint certificate pair in
a `(k,s)`-free graph with `5 ≤ k ≤ s` admits one of the four explicit
primal/dual normal forms. -/
theorem exists_plus_orientation
    (cert : Certificates G k s)
    (hG : IsRamseyFree G k s)
    (hk : 5 ≤ k) (hks : k ≤ s) :
    Nonempty (PlusOrientation G k s) := by
  have hs : 5 ≤ s := le_trans hk hks
  rcases exists_plus_normal_form_or_failure cert hG hk hs with
    hA | hB | hfailure
  · obtain ⟨data⟩ := hA
    exact ⟨.primalA data⟩
  · obtain ⟨data⟩ := hB
    exact ⟨.primalB data⟩
  · rcases exists_plus_normal_form_or_failure
      cert.dual hG.symm hs hk with hA | hB | hdualFailure
    · obtain ⟨data⟩ := hA
      exact ⟨.dualA data⟩
    · obtain ⟨data⟩ := hB
      exact ⟨.dualB data⟩
    · exact False.elim
        (orientation_counting_contradiction
          cert hG hk hs hks hfailure hdualFailure)

end Certificates

end RamseyIncrement
