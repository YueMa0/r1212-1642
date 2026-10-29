import RamseyIncrement.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# Ordered clique certificates

This file formalizes Section 1 of the proof.  A certificate consists of an
ordered red `K_(k-1)` and an ordered blue `K_(s-1)` with disjoint ranges.  It
defines the two branch-local normal forms used by the switching construction;
the four-way orientation theorem that produces them is in
`PlusCertificates.lean`.

No Ramsey-number or XSR assumption occurs here: those assumptions are only
needed later to produce the initial unordered certificates.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-- An ordered enumeration of a red `K_(k-1)` and a disjoint blue
`K_(s-1)`.  At this stage the enumerations have no special normal form. -/
structure Certificates (G : SimpleGraph V) (k s : ℕ) where
  c : Fin (k - 1) ↪ V
  i : Fin (s - 1) ↪ V
  c_isClique : G.IsClique (Set.range c)
  i_isClique : Gᶜ.IsClique (Set.range i)
  disjoint : Disjoint (Set.range c) (Set.range i)

namespace Certificates

/-- The canonical inclusion of the `C` indices into the `I` indices. -/
def castIndex (hks : k ≤ s) : Fin (k - 1) ↪ Fin (s - 1) where
  toFun p := ⟨p, by omega⟩
  inj' x y h := by
    apply Fin.ext
    simpa using congrArg Fin.val h

@[simp]
theorem castIndex_val (hks : k ≤ s) (p : Fin (k - 1)) :
    (castIndex hks p).val = p.val :=
  rfl

/-- Index zero in a nonempty finite index type. -/
def indexZero {n : ℕ} (h : 1 ≤ n) : Fin n :=
  ⟨0, h⟩

/-- Index one in a finite index type of cardinality at least two. -/
def indexOne {n : ℕ} (h : 2 ≤ n) : Fin n :=
  ⟨1, h⟩

@[simp] theorem indexZero_val {n : ℕ} (h : 1 ≤ n) : (indexZero h).val = 0 := rfl
@[simp] theorem indexOne_val {n : ℕ} (h : 2 ≤ n) : (indexOne h).val = 1 := rfl

/-- Distinct certificate blocks really have distinct vertices. -/
theorem c_ne_i (cert : Certificates G k s) (p : Fin (k - 1)) (q : Fin (s - 1)) :
    cert.c p ≠ cert.i q := by
  intro h
  have hc : cert.c p ∈ Set.range cert.c := Set.mem_range_self p
  have hi : cert.c p ∈ Set.range cert.i := ⟨q, h.symm⟩
  exact Set.disjoint_left.1 cert.disjoint hc hi

/-- The red adjacency supplied by the `C` clique. -/
theorem c_adj (cert : Certificates G k s) {p q : Fin (k - 1)} (hpq : p ≠ q) :
    G.Adj (cert.c p) (cert.c q) :=
  cert.c_isClique (Set.mem_range_self p) (Set.mem_range_self q)
    (fun h ↦ hpq (cert.c.injective h))

/-- The blue adjacency supplied by the `I` clique. -/
theorem i_compl_adj (cert : Certificates G k s) {p q : Fin (s - 1)} (hpq : p ≠ q) :
    Gᶜ.Adj (cert.i p) (cert.i q) :=
  cert.i_isClique (Set.mem_range_self p) (Set.mem_range_self q)
    (fun h ↦ hpq (cert.i.injective h))

/-- `β(q)`: the indices of the blue neighbors in `C` of `i_q`. -/
noncomputable def beta (cert : Certificates G k s) (q : Fin (s - 1)) :
    Finset (Fin (k - 1)) := by
  classical
  exact Finset.univ.filter fun p ↦ ¬G.Adj (cert.c p) (cert.i q)

@[simp]
theorem mem_beta (cert : Certificates G k s) (p : Fin (k - 1)) (q : Fin (s - 1)) :
    p ∈ cert.beta q ↔ ¬G.Adj (cert.c p) (cert.i q) := by
  classical
  simp [beta]

/-- The singleton-witness condition used by the Type B normal form. -/
def IsUniqueBlueWitness (cert : Certificates G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1)) : Prop :=
  cert.beta q = {p}

@[simp]
theorem isUniqueBlueWitness_iff (cert : Certificates G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    cert.IsUniqueBlueWitness p q ↔ cert.beta q = {p} :=
  Iff.rfl

/-- In a `(k,s)`-free graph, every vertex of `I` has a blue neighbor in
`C`; otherwise it extends the red `K_(k-1)` to a red `K_k`. -/
theorem beta_nonempty (cert : Certificates G k s) (hG : IsRamseyFree G k s)
    (hk : 2 ≤ k) (q : Fin (s - 1)) :
    (cert.beta q).Nonempty := by
  classical
  by_contra hβ
  have hall : ∀ p : Fin (k - 1), G.Adj (cert.c p) (cert.i q) := by
    intro p
    by_contra hp
    exact hβ ⟨p, (cert.mem_beta p q).2 hp⟩
  let C : Finset V := Finset.univ.map cert.c
  have hiC : cert.i q ∉ C := by
    intro hi
    obtain ⟨p, -, hp⟩ := Finset.mem_map.1 hi
    exact cert.c_ne_i p q hp
  have hC : G.IsClique (C : Set V) := by
    simpa [C] using cert.c_isClique
  have hclique : G.IsClique (↑(insert (cert.i q) C) : Set V) := by
    rw [Finset.coe_insert]
    exact hC.insert fun v hv _ ↦ by
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hv
      exact (hall p).symm
  have hcard : (insert (cert.i q) C).card = k := by
    simp [hiC, C]
    omega
  exact hG.1 _ ⟨hclique, hcard⟩

/-- Dually, every vertex of `C` has a red neighbor in `I`; otherwise it
extends the blue `K_(s-1)` to a blue `K_s`. -/
theorem exists_red_neighbor (cert : Certificates G k s) (hG : IsRamseyFree G k s)
    (hs : 2 ≤ s) (p : Fin (k - 1)) :
    ∃ q : Fin (s - 1), G.Adj (cert.c p) (cert.i q) := by
  classical
  by_contra hred
  push Not at hred
  let I : Finset V := Finset.univ.map cert.i
  have hcI : cert.c p ∉ I := by
    intro hc
    obtain ⟨q, -, hq⟩ := Finset.mem_map.1 hc
    exact cert.c_ne_i p q hq.symm
  have hI : Gᶜ.IsClique (I : Set V) := by
    simpa [I] using cert.i_isClique
  have hclique : Gᶜ.IsClique (↑(insert (cert.c p) I) : Set V) := by
    rw [Finset.coe_insert]
    exact hI.insert fun v hv _ ↦ by
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hv
      simp [cert.c_ne_i p q, hred q]
  have hcard : (insert (cert.c p) I).card = s := by
    simp [hcI, I]
    omega
  exact hG.2 _ ⟨hclique, hcard⟩

/-- Reorder either certificate by permutations of its index set. -/
noncomputable def relabel (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1))) :
    Certificates G k s where
  c := ec.toEmbedding.trans cert.c
  i := ei.toEmbedding.trans cert.i
  c_isClique := by
    have hrange :
        Set.range (ec.toEmbedding.trans cert.c) = Set.range cert.c := by
      ext v
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨ec p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨ec.symm p, by simp⟩
    rw [hrange]
    exact cert.c_isClique
  i_isClique := by
    have hrange :
        Set.range (ei.toEmbedding.trans cert.i) = Set.range cert.i := by
      ext v
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨ei q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨ei.symm q, by simp⟩
    rw [hrange]
    exact cert.i_isClique
  disjoint := by
    have hc :
        Set.range (ec.toEmbedding.trans cert.c) = Set.range cert.c := by
      ext v
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨ec p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨ec.symm p, by simp⟩
    have hi :
        Set.range (ei.toEmbedding.trans cert.i) = Set.range cert.i := by
      ext v
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨ei q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨ei.symm q, by simp⟩
    simpa [hc, hi] using cert.disjoint

@[simp]
theorem relabel_c (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1)))
    (p : Fin (k - 1)) :
    (cert.relabel ec ei).c p = cert.c (ec p) :=
  rfl

@[simp]
theorem relabel_i (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1)))
    (q : Fin (s - 1)) :
    (cert.relabel ec ei).i q = cert.i (ei q) :=
  rfl

theorem relabel_c_range (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1))) :
    Set.range (cert.relabel ec ei).c = Set.range cert.c := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨ec p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨ec.symm p, by simp⟩

theorem relabel_i_range (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1))) :
    Set.range (cert.relabel ec ei).i = Set.range cert.i := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨ei q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨ei.symm q, by simp⟩

/-- Relabeling transports singleton `β`-certificates equivariantly. -/
theorem relabel_unique_iff (cert : Certificates G k s)
    (ec : Equiv.Perm (Fin (k - 1))) (ei : Equiv.Perm (Fin (s - 1)))
    (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (cert.relabel ec ei).beta q = {p} ↔ cert.beta (ei q) = {ec p} := by
  classical
  constructor
  · intro h
    ext r
    have hm := Finset.ext_iff.1 h (ec.symm r)
    simpa [Equiv.symm_apply_eq] using hm
  · intro h
    ext r
    have hm := Finset.ext_iff.1 h (ec r)
    simpa using hm

/-- The index called `0` in the red certificate. -/
def c0Index (hk : 5 ≤ k) : Fin (k - 1) :=
  indexZero (by omega)

/-- The index called `1` in the red certificate. -/
def c1Index (hk : 5 ≤ k) : Fin (k - 1) :=
  indexOne (by omega)

/-- The index called `2` in the red certificate. -/
def c2Index (hk : 5 ≤ k) : Fin (k - 1) :=
  ⟨2, by omega⟩

/-- The index called `0` in the blue certificate. -/
def i0Index' (hs : 5 ≤ s) : Fin (s - 1) :=
  indexZero (by omega)

/-- The index called `1` in the blue certificate. -/
def i1Index' (hs : 5 ≤ s) : Fin (s - 1) :=
  indexOne (by omega)

/-- The index called `2` in the blue certificate. -/
def i2Index' (hs : 5 ≤ s) : Fin (s - 1) :=
  ⟨2, by omega⟩

@[simp] theorem c0Index_val (hk : 5 ≤ k) : (c0Index hk).val = 0 := rfl
@[simp] theorem c1Index_val (hk : 5 ≤ k) : (c1Index hk).val = 1 := rfl
@[simp] theorem c2Index_val (hk : 5 ≤ k) : (c2Index hk).val = 2 := rfl
@[simp] theorem i0Index'_val (hs : 5 ≤ s) : (i0Index' hs).val = 0 := rfl
@[simp] theorem i1Index'_val (hs : 5 ≤ s) : (i1Index' hs).val = 1 := rfl
@[simp] theorem i2Index'_val (hs : 5 ≤ s) : (i2Index' hs).val = 2 := rfl

theorem c0_ne_c1 (hk : 5 ≤ k) : c0Index hk ≠ c1Index hk := by
  intro h
  have := congrArg Fin.val h
  simp at this

@[simp]
theorem castIndex_c0' (hk : 5 ≤ k) (hs : 5 ≤ s) (hks : k ≤ s) :
    castIndex hks (c0Index hk) = i0Index' hs := by
  apply Fin.ext
  rfl

@[simp]
theorem castIndex_c1' (hk : 5 ≤ k) (hs : 5 ≤ s) (hks : k ≤ s) :
    castIndex hks (c1Index hk) = i1Index' hs := by
  apply Fin.ext
  rfl

@[simp]
theorem castIndex_c2' (hk : 5 ≤ k) (hs : 5 ≤ s) (hks : k ≤ s) :
    castIndex hks (c2Index hk) = i2Index' hs := by
  apply Fin.ext
  rfl

/-- Case A of the certificate ordering: index `1` is not the unique blue
neighbor of any `i_q`, and `c_0 i_0` is red. -/
def IsCaseA (cert : Certificates G k s) (hk : 5 ≤ k) (hs : 5 ≤ s) : Prop :=
  (∀ q : Fin (s - 1), ¬cert.IsUniqueBlueWitness (c1Index hk) q) ∧
    G.Adj (cert.c (c0Index hk)) (cert.i (i0Index' hs))

/-- Case B of the certificate ordering: the first `k-1` vertices of `I`
are the distinct singleton witnesses from equation (5B). -/
def IsCaseB (cert : Certificates G k s) (_hk : 5 ≤ k) (hks : k ≤ s) : Prop :=
  ∀ p : Fin (k - 1), cert.IsUniqueBlueWitness p (castIndex hks p)

/-- The data specific to Case B.  In particular, parameter order is local
to this branch rather than an invariant of all ordered certificates. -/
structure CaseBData (cert : Certificates G k s) (hk : 5 ≤ k) where
  k_le_s : k ≤ s
  witnesses : cert.IsCaseB hk k_le_s

/-- The two normal forms cannot occur simultaneously. -/
theorem caseA_caseBData_disjoint (cert : Certificates G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s) :
    ¬(cert.IsCaseA hk hs ∧ Nonempty (CaseBData cert hk)) := by
  rintro ⟨hA, ⟨hB⟩⟩
  exact hA.1 (castIndex hB.k_le_s (c1Index hk))
    (hB.witnesses (c1Index hk))

/-- The branch-local normal form used by the switching construction. -/
inductive NormalForm (cert : Certificates G k s)
    (hk : 5 ≤ k) (hs : 5 ≤ s) : Type
  | caseA (hA : cert.IsCaseA hk hs)
  | caseB (hB : CaseBData cert hk)

/-- Ordered certificates carry exactly the hypotheses needed by the
switching construction. -/
structure OrderedCertificates (G : SimpleGraph V) (k s : ℕ)
    extends Certificates G k s where
  five_le_k : 5 ≤ k
  five_le_s : 5 ≤ s
  normal : NormalForm toCertificates five_le_k five_le_s

namespace OrderedCertificates

theorem two_le_s (cert : OrderedCertificates G k s) : 2 ≤ s := by
  exact le_trans (by decide : 2 ≤ 5) cert.five_le_s

/-- The normal-form alternatives are exclusive as well as exhaustive. -/
theorem normal_xor (cert : OrderedCertificates G k s) :
    Xor (cert.toCertificates.IsCaseA cert.five_le_k cert.five_le_s)
      (Nonempty (CaseBData cert.toCertificates cert.five_le_k)) := by
  rcases cert.normal with hA | hB
  · exact Or.inl ⟨hA, fun hB ↦
      Certificates.caseA_caseBData_disjoint _ _ _ ⟨hA, hB⟩⟩
  · exact Or.inr ⟨⟨hB⟩, fun hA ↦
      Certificates.caseA_caseBData_disjoint _ _ _ ⟨hA, ⟨hB⟩⟩⟩

end OrderedCertificates

namespace OrderedCertificates

/-- The set `T` from equation (7). -/
noncomputable def T (cert : OrderedCertificates G k s) : Finset (Fin (s - 1)) := by
  classical
  exact Finset.univ.filter fun q ↦
    G.Adj (cert.c (c0Index cert.five_le_k)) (cert.i q)

/-- The set `E` from equation (7). -/
noncomputable def E (cert : OrderedCertificates G k s) : Finset (Fin (s - 1)) := by
  classical
  exact cert.T.filter fun q ↦
    ∀ p : Fin (k - 1), 2 ≤ p.val → G.Adj (cert.c p) (cert.i q)

/-- The set `S = T \ E` from equation (7). -/
noncomputable def S (cert : OrderedCertificates G k s) : Finset (Fin (s - 1)) :=
  cert.T \ cert.E

/-- The set `U = {0,...,s-2} \ T` from equation (7). -/
noncomputable def U (cert : OrderedCertificates G k s) : Finset (Fin (s - 1)) :=
  Finset.univ \ cert.T

@[simp]
theorem mem_T (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.T ↔ G.Adj (cert.c (c0Index cert.five_le_k)) (cert.i q) := by
  classical
  simp [T]

@[simp]
theorem mem_E (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.E ↔
      q ∈ cert.T ∧
        ∀ p : Fin (k - 1), 2 ≤ p.val → G.Adj (cert.c p) (cert.i q) := by
  classical
  simp [E]

@[simp]
theorem mem_S (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.S ↔ q ∈ cert.T ∧ q ∉ cert.E := by
  classical
  simp [S]

@[simp]
theorem mem_U (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.U ↔ q ∉ cert.T := by
  classical
  simp [U]

theorem E_subset_T (cert : OrderedCertificates G k s) : cert.E ⊆ cert.T := by
  intro q hq
  exact (cert.mem_E q).1 hq |>.1

theorem S_subset_T (cert : OrderedCertificates G k s) : cert.S ⊆ cert.T := by
  intro q hq
  exact (cert.mem_S q).1 hq |>.1

theorem E_disjoint_S (cert : OrderedCertificates G k s) :
    Disjoint cert.E cert.S := by
  exact Finset.disjoint_left.2 fun _ hE hS ↦ ((cert.mem_S _).1 hS).2 hE

theorem T_disjoint_U (cert : OrderedCertificates G k s) :
    Disjoint cert.T cert.U := by
  exact Finset.disjoint_left.2 fun _ hT hU ↦ ((cert.mem_U _).1 hU) hT

theorem T_eq_E_union_S (cert : OrderedCertificates G k s) :
    cert.T = cert.E ∪ cert.S := by
  classical
  ext q
  constructor
  · intro hT
    by_cases hE : q ∈ cert.E
    · exact Finset.mem_union_left _ hE
    · exact Finset.mem_union_right _ ((cert.mem_S q).2 ⟨hT, hE⟩)
  · intro h
    rcases Finset.mem_union.1 h with hE | hS
    · exact cert.E_subset_T hE
    · exact cert.S_subset_T hS

theorem univ_eq_T_union_U (cert : OrderedCertificates G k s) :
    Finset.univ = cert.T ∪ cert.U := by
  classical
  ext q
  by_cases hT : q ∈ cert.T <;> simp [hT]

/-- If `q ∈ E`, all possible blue neighbors of `i_q` except `c_1`
have been ruled out.  Nonemptiness of `β(q)` then makes `c_1` its unique
blue neighbor. -/
theorem beta_eq_c1_of_mem_E (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) {q : Fin (s - 1)} (hq : q ∈ cert.E) :
    cert.beta q = {c1Index cert.five_le_k} := by
  classical
  have hqE := (cert.mem_E q).1 hq
  have hsubset :
      cert.beta q ⊆ {c1Index cert.five_le_k} := by
    intro p hp
    simp only [Finset.mem_singleton]
    by_contra hp1
    by_cases hp0val : p.val = 0
    · have hp0 : p = c0Index cert.five_le_k := by
        apply Fin.ext
        simpa using hp0val
      exact ((cert.mem_beta p q).1 hp)
        (by simpa [hp0] using (cert.mem_T q).1 hqE.1)
    · have hp2 : 2 ≤ p.val := by
        have hp1val : p.val ≠ 1 := by
          intro hpval
          apply hp1
          apply Fin.ext
          simpa using hpval
        omega
      exact ((cert.mem_beta p q).1 hp) (hqE.2 p hp2)
  obtain ⟨p, hp⟩ :=
    cert.toCertificates.beta_nonempty hG
      (le_trans (by decide : 2 ≤ 5) cert.five_le_k) q
  apply Finset.eq_singleton_iff_unique_mem.2
  constructor
  · have hp1 : p = c1Index cert.five_le_k := by
      simpa using hsubset hp
    rwa [← hp1]
  · intro r hr
    simpa using hsubset hr

/-- Case A forces `E = ∅`. -/
theorem caseA_E_eq_empty (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hA : cert.toCertificates.IsCaseA cert.five_le_k cert.five_le_s) :
    cert.E = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.1
  rintro ⟨q, hq⟩
  exact hA.1 q (cert.beta_eq_c1_of_mem_E hG hq)

/-- The distinguished Case A index belongs to `S`. -/
theorem caseA_i0_mem_S (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hA : cert.toCertificates.IsCaseA cert.five_le_k cert.five_le_s) :
    i0Index' cert.five_le_s ∈ cert.S := by
  rw [cert.mem_S]
  constructor
  · exact (cert.mem_T _).2 hA.2
  · rw [cert.caseA_E_eq_empty hG hA]
    simp

/-- The matched edge of a Case B witness is blue. -/
theorem caseB_not_adj_matched (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k)
    (p : Fin (k - 1)) :
    ¬G.Adj (cert.c p) (cert.i (castIndex hB.k_le_s p)) := by
  exact (cert.mem_beta p (castIndex hB.k_le_s p)).1 (by
    rw [hB.witnesses p]
    simp)

/-- Every nonmatched `C` edge to a Case B witness is red. -/
theorem caseB_adj_of_ne (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k)
    {p r : Fin (k - 1)} (hrp : r ≠ p) :
    G.Adj (cert.c r) (cert.i (castIndex hB.k_le_s p)) := by
  by_contra hred
  have hrβ :=
    (cert.mem_beta r (castIndex hB.k_le_s p)).2 hred
  rw [hB.witnesses p] at hrβ
  exact hrp (by simpa using hrβ)

/-- First assertion of (7B): `0 ∈ U` in Case B. -/
theorem caseB_i0_mem_U (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    i0Index' cert.five_le_s ∈ cert.U := by
  rw [cert.mem_U, cert.mem_T,
    ← castIndex_c0' cert.five_le_k cert.five_le_s hB.k_le_s]
  exact cert.caseB_not_adj_matched hB (c0Index cert.five_le_k)

/-- Second assertion of (7B): `1 ∈ E` in Case B. -/
theorem caseB_i1_mem_E (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    i1Index' cert.five_le_s ∈ cert.E := by
  rw [cert.mem_E]
  constructor
  · rw [cert.mem_T,
      ← castIndex_c1' cert.five_le_k cert.five_le_s hB.k_le_s]
    exact cert.caseB_adj_of_ne hB (c0_ne_c1 cert.five_le_k)
  · intro p hp2
    rw [← castIndex_c1' cert.five_le_k cert.five_le_s hB.k_le_s]
    apply cert.caseB_adj_of_ne hB
    intro hp
    have := congrArg Fin.val hp
    simp at this
    omega

/-- Third assertion of (7B): every Case B witness index from `2` through
`k-2` belongs to `S`. -/
theorem caseB_castIndex_mem_S (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k)
    (p : Fin (k - 1)) (hp2 : 2 ≤ p.val) :
    castIndex hB.k_le_s p ∈ cert.S := by
  rw [cert.mem_S]
  constructor
  · rw [cert.mem_T]
    apply cert.caseB_adj_of_ne hB
    intro hp
    have := congrArg Fin.val hp
    simp at this
    omega
  · intro hpE
    have hpAdj := ((cert.mem_E _).1 hpE).2 p hp2
    exact cert.caseB_not_adj_matched hB p hpAdj

/-- Equation (7b): in normal form, `E` is nonempty exactly when its
distinguished index `1` lies in `E`. -/
theorem E_nonempty_iff_i1_mem (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    cert.E.Nonempty ↔ i1Index' cert.five_le_s ∈ cert.E := by
  rcases cert.normal with hA | hB
  · rw [cert.caseA_E_eq_empty hG hA]
    simp
  · exact ⟨fun _ ↦ cert.caseB_i1_mem_E hB,
      fun h ↦ ⟨i1Index' cert.five_le_s, h⟩⟩

/-- A useful strengthening of (7b): nonempty `E` yields the complete
branch-local Case B data. -/
theorem caseBData_of_E_nonempty (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    cert.E.Nonempty → CaseBData cert.toCertificates cert.five_le_k := by
  intro hE
  rcases cert.normal with hA | hB
  · rw [cert.caseA_E_eq_empty hG hA] at hE
    simp at hE
  · exact hB

/-- Propositional form of the characterization of the Case B branch. -/
theorem E_nonempty_iff_caseB (cert : OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    cert.E.Nonempty ↔
      Nonempty (CaseBData cert.toCertificates cert.five_le_k) := by
  constructor
  · exact fun hE ↦ ⟨cert.caseBData_of_E_nonempty hG hE⟩
  · rintro ⟨hB⟩
    exact ⟨i1Index' cert.five_le_s, cert.caseB_i1_mem_E hB⟩

/-- Shift a tail index by two.  Its range is exactly the indices
`2, ..., n-2` in `Fin (n-1)`. -/
def tailEmbedding {n : ℕ} (hn : 3 ≤ n) : Fin (n - 3) ↪ Fin (n - 1) where
  toFun p := ⟨p.val + 2, by omega⟩
  inj' p q h := by
    apply Fin.ext
    have := congrArg Fin.val h
    simp only at this
    omega

@[simp]
theorem tailEmbedding_val {n : ℕ} (hn : 3 ≤ n) (p : Fin (n - 3)) :
    (tailEmbedding hn p).val = p.val + 2 :=
  rfl

/-- The ordinary large indices `{2, ..., s-2}`. -/
noncomputable def largeIndices (cert : OrderedCertificates G k s) :
    Finset (Fin (s - 1)) :=
  Finset.univ.map (tailEmbedding (by
    exact le_trans (by decide : 3 ≤ 5) cert.five_le_s))

@[simp]
theorem card_largeIndices (cert : OrderedCertificates G k s) :
    cert.largeIndices.card = s - 3 := by
  classical
  simp [largeIndices]

theorem mem_largeIndices_iff (cert : OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    q ∈ cert.largeIndices ↔ 2 ≤ q.val := by
  classical
  constructor
  · intro hq
    obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hq
    simp
  · intro hq
    let p : Fin (s - 3) := ⟨q.val - 2, by
      have hq_lt := q.isLt
      omega⟩
    apply Finset.mem_map.2
    refine ⟨p, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [p]
    omega

/-- `E_lg` from the manuscript. -/
noncomputable def ELarge (cert : OrderedCertificates G k s) :
    Finset (Fin (s - 1)) :=
  cert.E ∩ cert.largeIndices

/-- The analogous large-index part of `S`. -/
noncomputable def SLarge (cert : OrderedCertificates G k s) :
    Finset (Fin (s - 1)) :=
  cert.S ∩ cert.largeIndices

/-- `U_lg` from the manuscript. -/
noncomputable def ULarge (cert : OrderedCertificates G k s) :
    Finset (Fin (s - 1)) :=
  cert.U ∩ cert.largeIndices

@[simp]
theorem mem_ELarge (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.ELarge ↔ q ∈ cert.E ∧ 2 ≤ q.val := by
  classical
  simp [ELarge, cert.mem_largeIndices_iff]

@[simp]
theorem mem_SLarge (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.SLarge ↔ q ∈ cert.S ∧ 2 ≤ q.val := by
  classical
  simp [SLarge, cert.mem_largeIndices_iff]

@[simp]
theorem mem_ULarge (cert : OrderedCertificates G k s) (q : Fin (s - 1)) :
    q ∈ cert.ULarge ↔ q ∈ cert.U ∧ 2 ≤ q.val := by
  classical
  simp [ULarge, cert.mem_largeIndices_iff]

theorem ELarge_disjoint_SLarge (cert : OrderedCertificates G k s) :
    Disjoint cert.ELarge cert.SLarge := by
  exact cert.E_disjoint_S.mono Finset.inter_subset_left Finset.inter_subset_left

theorem ELarge_disjoint_ULarge (cert : OrderedCertificates G k s) :
    Disjoint cert.ELarge cert.ULarge := by
  apply cert.T_disjoint_U.mono
  · exact fun _ hq ↦ cert.E_subset_T ((cert.mem_ELarge _).1 hq).1
  · exact Finset.inter_subset_left

theorem SLarge_disjoint_ULarge (cert : OrderedCertificates G k s) :
    Disjoint cert.SLarge cert.ULarge := by
  apply cert.T_disjoint_U.mono
  · exact fun _ hq ↦ cert.S_subset_T ((cert.mem_SLarge _).1 hq).1
  · exact Finset.inter_subset_left

/-- The large indices are partitioned by `E`, `S`, and `U`. -/
theorem largeIndices_eq_union (cert : OrderedCertificates G k s) :
    cert.largeIndices = (cert.ELarge ∪ cert.SLarge) ∪ cert.ULarge := by
  classical
  ext q
  constructor
  · intro hlarge
    by_cases hT : q ∈ cert.T
    · by_cases hE : q ∈ cert.E
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          ((cert.mem_ELarge q).2 ⟨hE, (cert.mem_largeIndices_iff q).1 hlarge⟩))
      · have hS : q ∈ cert.S := (cert.mem_S q).2 ⟨hT, hE⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((cert.mem_SLarge q).2 ⟨hS, (cert.mem_largeIndices_iff q).1 hlarge⟩))
    · have hU : q ∈ cert.U := (cert.mem_U q).2 hT
      exact Finset.mem_union_right _
        ((cert.mem_ULarge q).2 ⟨hU, (cert.mem_largeIndices_iff q).1 hlarge⟩)
  · intro h
    rcases Finset.mem_union.1 h with hES | hU
    · rcases Finset.mem_union.1 hES with hE | hS
      · exact Finset.inter_subset_right hE
      · exact Finset.inter_subset_right hS
    · exact Finset.inter_subset_right hU

/-- Cardinal form of the `E/S/U` partition of the large indices. -/
theorem card_ELarge_add_SLarge_add_ULarge (cert : OrderedCertificates G k s) :
    cert.ELarge.card + cert.SLarge.card + cert.ULarge.card = s - 3 := by
  classical
  have hESU : Disjoint (cert.ELarge ∪ cert.SLarge) cert.ULarge :=
    Finset.disjoint_union_left.2
      ⟨cert.ELarge_disjoint_ULarge, cert.SLarge_disjoint_ULarge⟩
  calc
    cert.ELarge.card + cert.SLarge.card + cert.ULarge.card =
        (cert.ELarge ∪ cert.SLarge).card + cert.ULarge.card := by
          rw [Finset.card_union_of_disjoint cert.ELarge_disjoint_SLarge]
    _ = ((cert.ELarge ∪ cert.SLarge) ∪ cert.ULarge).card := by
          rw [Finset.card_union_of_disjoint hESU]
    _ = cert.largeIndices.card := by rw [cert.largeIndices_eq_union]
    _ = s - 3 := cert.card_largeIndices

/-- The mandatory Case B indices `{2, ..., k-2}`, embedded into the
`I`-index type. -/
def mandatoryEmbedding (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    Fin (k - 3) ↪ Fin (s - 1) :=
  (tailEmbedding (le_trans (by decide : 3 ≤ 5) cert.five_le_k)).trans
    (castIndex hB.k_le_s)

@[simp]
theorem mandatoryEmbedding_val (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k)
    (p : Fin (k - 3)) :
    (cert.mandatoryEmbedding hB p).val = p.val + 2 :=
  rfl

noncomputable def mandatoryIndices (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    Finset (Fin (s - 1)) :=
  Finset.univ.map (cert.mandatoryEmbedding hB)

@[simp]
theorem card_mandatoryIndices (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    (cert.mandatoryIndices hB).card = k - 3 := by
  classical
  simp [mandatoryIndices]

theorem caseB_mandatory_subset_SLarge (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    cert.mandatoryIndices hB ⊆ cert.SLarge := by
  classical
  intro q hq
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hq
  apply (cert.mem_SLarge _).2
  constructor
  · exact cert.caseB_castIndex_mem_S hB
      (tailEmbedding (le_trans (by decide : 3 ≤ 5) cert.five_le_k) p) (by simp)
  · simp

theorem caseB_k_sub_three_le_card_SLarge (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    k - 3 ≤ cert.SLarge.card := by
  rw [← cert.card_mandatoryIndices hB]
  exact Finset.card_le_card (cert.caseB_mandatory_subset_SLarge hB)

/-- First inequality in (7a), with `m = |E_lg|`. -/
theorem caseB_card_ELarge_le (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    cert.ELarge.card ≤ s - k := by
  have hpartition := cert.card_ELarge_add_SLarge_add_ULarge
  have hmandatory := cert.caseB_k_sub_three_le_card_SLarge hB
  have hk := cert.five_le_k
  have hks := hB.k_le_s
  omega

/-- Second inequality in (7a), with `m = |E_lg|`. -/
theorem caseB_card_ULarge_le (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    cert.ULarge.card ≤ s - k - cert.ELarge.card := by
  have hpartition := cert.card_ELarge_add_SLarge_add_ULarge
  have hmandatory := cert.caseB_k_sub_three_le_card_SLarge hB
  have hk := cert.five_le_k
  have hks := hB.k_le_s
  omega

/-- Equation (7a), bundled in the form used by later switching counts. -/
theorem caseB_large_bounds (cert : OrderedCertificates G k s)
    (hB : CaseBData cert.toCertificates cert.five_le_k) :
    cert.ELarge.card ≤ s - k ∧
      cert.ULarge.card ≤ s - k - cert.ELarge.card :=
  ⟨cert.caseB_card_ELarge_le hB, cert.caseB_card_ULarge_le hB⟩

end OrderedCertificates

end Certificates

end RamseyIncrement
