/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Construction

/-!
# The six blocks of the switched vertex type

The first connector is implemented using nested tagged sums.  This file
provides the flat six-block view needed by the second-connector clique
arguments, while continuing to use the actual `Switching.Vertex` type.
-/

namespace RamseyIncrement
namespace SecondConnector

open Finset

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- The six structural blocks in `Switching.Vertex`. -/
inductive BlockTag
  | core
  | a
  | b
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- Read the flat block tag from the nested representation used by the
switching construction. -/
def blockTag : Switching.Vertex V k s → BlockTag
  | .inl (.core (.core _)) => .core
  | .inl (.core (.a _)) => .a
  | .inl (.core (.b _)) => .b
  | .inl (.a _) => .x
  | .inl (.b _) => .y
  | .inr _ => .z

@[simp]
theorem blockTag_core (v : V) :
    blockTag (Switching.Vertex.core (k := k) (s := s) v) = .core :=
  rfl

@[simp]
theorem blockTag_a (p : Fin (k - 1)) :
    blockTag (Switching.Vertex.a (V := V) (s := s) p) = .a :=
  rfl

@[simp]
theorem blockTag_b (p : Fin (k - 1)) :
    blockTag (Switching.Vertex.b (V := V) (s := s) p) = .b :=
  rfl

@[simp]
theorem blockTag_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    blockTag (Switching.Vertex.x cert r) = .x :=
  rfl

@[simp]
theorem blockTag_y
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    blockTag (Switching.Vertex.y cert r) = .y :=
  rfl

@[simp]
theorem blockTag_z :
    blockTag (Switching.Vertex.z : Switching.Vertex V k s) = .z :=
  rfl

/-- Different block fibers are disjoint. -/
theorem blockTag_fibers_disjoint {i j : BlockTag} (hij : i ≠ j) :
    Disjoint
      {v : Switching.Vertex V k s | blockTag v = i}
      {v : Switching.Vertex V k s | blockTag v = j} := by
  rw [Set.disjoint_left]
  intro v hi hj
  exact hij (hi.symm.trans hj)

theorem vertex_core_injective :
    Function.Injective
      (Switching.Vertex.core :
        V → Switching.Vertex V k s) := by
  intro u v h
  exact SpecialLiftVertex.core.inj
    (SpecialLiftVertex.core.inj (Sum.inl.inj h))

theorem vertex_a_injective :
    Function.Injective
      (Switching.Vertex.a :
        Fin (k - 1) → Switching.Vertex V k s) := by
  intro p q h
  exact SpecialLiftVertex.a.inj
    (SpecialLiftVertex.core.inj (Sum.inl.inj h))

theorem vertex_b_injective :
    Function.Injective
      (Switching.Vertex.b :
        Fin (k - 1) → Switching.Vertex V k s) := by
  intro p q h
  exact SpecialLiftVertex.b.inj
    (SpecialLiftVertex.core.inj (Sum.inl.inj h))

theorem vertex_x_injective
    (cert : Certificates.OrderedCertificates G k s) :
    Function.Injective (Switching.Vertex.x cert) := by
  intro r q h
  have hindex :
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm r =
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm q :=
    SpecialLiftVertex.a.inj (Sum.inl.inj h)
  exact (Canonical.outerIndexEquiv
    (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm.injective hindex

theorem vertex_y_injective
    (cert : Certificates.OrderedCertificates G k s) :
    Function.Injective (Switching.Vertex.y cert) := by
  intro r q h
  have hindex :
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm r =
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm q :=
    SpecialLiftVertex.b.inj (Sum.inl.inj h)
  exact (Canonical.outerIndexEquiv
    (le_trans (by decide : 1 ≤ 5) cert.five_le_s)).symm.injective hindex

/-- Every switched vertex belongs to exactly one of the six displayed
families.  The `X` and `Y` indices use the public optional-index
presentation, rather than the raw outer-lift indices. -/
theorem vertex_six_block_cases
    (cert : Certificates.OrderedCertificates G k s)
    (w : Switching.Vertex V k s) :
    (∃ v, w = Switching.Vertex.core v) ∨
    (∃ p, w = Switching.Vertex.a p) ∨
    (∃ p, w = Switching.Vertex.b p) ∨
    (∃ r, w = Switching.Vertex.x cert r) ∨
    (∃ r, w = Switching.Vertex.y cert r) ∨
      w = Switching.Vertex.z := by
  rcases w with (w | u)
  · rcases w with (w | q | q)
    · rcases w with (v | p | p)
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr (Or.inl ⟨p, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨p, rfl⟩))
    · right
      right
      right
      left
      let e := Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)
      exact ⟨e q, by simp [Switching.Vertex.x, e]⟩
    · right
      right
      right
      right
      left
      let e := Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) cert.five_le_s)
      exact ⟨e q, by simp [Switching.Vertex.y, e]⟩
  · right
    right
    right
    right
    right
    cases u
    rfl

/-- Core vertices of a finite switched set, with their tags removed. -/
abbrev CoreIn (K : Finset (Switching.Vertex V k s)) :=
  {v : V // Switching.Vertex.core v ∈ K}

/-- `A` vertices of a finite switched set, with their tags removed. -/
abbrev AIn (K : Finset (Switching.Vertex V k s)) :=
  {p : Fin (k - 1) // Switching.Vertex.a p ∈ K}

/-- `B` vertices of a finite switched set, with their tags removed. -/
abbrev BIn (K : Finset (Switching.Vertex V k s)) :=
  {p : Fin (k - 1) // Switching.Vertex.b p ∈ K}

/-- `X` vertices of a finite switched set, using the optional index
presentation in `Switching.Vertex.x`. -/
abbrev XIn
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :=
  {r : Option (Fin (s - 1)) // Switching.Vertex.x cert r ∈ K}

/-- `Y` vertices of a finite switched set, using the optional index
presentation in `Switching.Vertex.y`. -/
abbrev YIn
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :=
  {r : Option (Fin (s - 1)) // Switching.Vertex.y cert r ∈ K}

/-- The singleton `Z` block of a finite switched set. -/
abbrev ZIn (K : Finset (Switching.Vertex V k s)) :=
  {_u : Unit // (Switching.Vertex.z : Switching.Vertex V k s) ∈ K}

instance coreInFinite (K : Finset (Switching.Vertex V k s)) :
    Finite (CoreIn K) :=
  Finite.of_injective
    (fun d : CoreIn K =>
      (⟨Switching.Vertex.core d.1, d.2⟩ :
        {x : Switching.Vertex V k s // x ∈ K}))
    (fun _ _ h ↦ Subtype.ext (vertex_core_injective
      (congrArg Subtype.val h)))

instance aInFinite (K : Finset (Switching.Vertex V k s)) :
    Finite (AIn K) :=
  Finite.of_injective
    (fun p : AIn K =>
      (⟨Switching.Vertex.a p.1, p.2⟩ :
        {x : Switching.Vertex V k s // x ∈ K}))
    (fun _ _ h ↦ Subtype.ext (vertex_a_injective
      (congrArg Subtype.val h)))

instance bInFinite (K : Finset (Switching.Vertex V k s)) :
    Finite (BIn K) :=
  Finite.of_injective
    (fun p : BIn K =>
      (⟨Switching.Vertex.b p.1, p.2⟩ :
        {x : Switching.Vertex V k s // x ∈ K}))
    (fun _ _ h ↦ Subtype.ext (vertex_b_injective
      (congrArg Subtype.val h)))

instance xInFinite
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Finite (XIn cert K) :=
  Finite.of_injective
    (fun r : XIn cert K =>
      (⟨Switching.Vertex.x cert r.1, r.2⟩ :
        {x : Switching.Vertex V k s // x ∈ K}))
    (fun _ _ h ↦ Subtype.ext (vertex_x_injective cert
      (congrArg Subtype.val h)))

instance yInFinite
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Finite (YIn cert K) :=
  Finite.of_injective
    (fun r : YIn cert K =>
      (⟨Switching.Vertex.y cert r.1, r.2⟩ :
        {x : Switching.Vertex V k s // x ∈ K}))
    (fun _ _ h ↦ Subtype.ext (vertex_y_injective cert
      (congrArg Subtype.val h)))

instance zInFinite (K : Finset (Switching.Vertex V k s)) :
    Finite (ZIn K) :=
  Finite.of_injective
    (fun u : ZIn K => u.1)
    Subtype.val_injective

noncomputable instance coreInFintype
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (CoreIn K) :=
  Fintype.ofFinite _

noncomputable instance aInFintype
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (AIn K) :=
  Fintype.ofFinite _

noncomputable instance bInFintype
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (BIn K) :=
  Fintype.ofFinite _

noncomputable instance xInFintype
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (XIn cert K) :=
  Fintype.ofFinite _

noncomputable instance yInFintype
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (YIn cert K) :=
  Fintype.ofFinite _

noncomputable instance zInFintype
    (K : Finset (Switching.Vertex V k s)) :
    Fintype (ZIn K) :=
  Fintype.ofFinite _

/-- Partition a finite set of actual switched vertices into the six flat
blocks used in the paper. -/
def switchingSetEquiv
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    {x // x ∈ K} ≃
      CoreIn K ⊕
        (AIn K ⊕
          (BIn K ⊕
            (XIn cert K ⊕ (YIn cert K ⊕ ZIn K)))) where
  toFun x :=
    match x.1, x.2 with
    | .inl (.core (.core v)), hv =>
        Sum.inl ⟨v, hv⟩
    | .inl (.core (.a p)), hp =>
        Sum.inr (Sum.inl ⟨p, hp⟩)
    | .inl (.core (.b p)), hp =>
        Sum.inr (Sum.inr (Sum.inl ⟨p, hp⟩))
    | .inl (.a q), hq =>
        let e := Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) cert.five_le_s)
        Sum.inr (Sum.inr (Sum.inr
          (Sum.inl ⟨e q, by
            simpa [Switching.Vertex.x, e] using hq⟩)))
    | .inl (.b q), hq =>
        let e := Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5) cert.five_le_s)
        Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inl ⟨e q, by
            simpa [Switching.Vertex.y, e] using hq⟩))))
    | .inr u, hz =>
        Sum.inr (Sum.inr (Sum.inr
          (Sum.inr (Sum.inr ⟨u, by
            cases u
            exact hz⟩))))
  invFun
    | Sum.inl v =>
        ⟨Switching.Vertex.core v.1, v.2⟩
    | Sum.inr (Sum.inl p) =>
        ⟨Switching.Vertex.a p.1, p.2⟩
    | Sum.inr (Sum.inr (Sum.inl p)) =>
        ⟨Switching.Vertex.b p.1, p.2⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) =>
        ⟨Switching.Vertex.x cert r.1, r.2⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl r)))) =>
        ⟨Switching.Vertex.y cert r.1, r.2⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))) =>
        ⟨Switching.Vertex.z, u.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rcases x with (x | u)
    · rcases x with (x | q | q)
      · rcases x with (v | p | p) <;> rfl
      · simp [Switching.Vertex.x]
      · simp [Switching.Vertex.y]
    · cases u
      rfl
  right_inv x := by
    rcases x with (v | p | p | r | r | u)
    · rfl
    · rfl
    · rfl
    · simp [Switching.Vertex.x]
    · simp [Switching.Vertex.y]
    · rcases u with ⟨u, hu⟩
      cases u
      rfl

/-- Cardinal decomposition of a finite switched set into its six
structural blocks. -/
theorem card_eq_six_blocks
    (cert : Certificates.OrderedCertificates G k s)
    (K : Finset (Switching.Vertex V k s)) :
    K.card =
      Fintype.card (CoreIn K) +
      Fintype.card (AIn K) +
      Fintype.card (BIn K) +
      Fintype.card (XIn cert K) +
      Fintype.card (YIn cert K) +
      Fintype.card (ZIn K) := by
  classical
  rw [← Fintype.card_coe K,
    Fintype.card_congr (switchingSetEquiv cert K)]
  simp
  omega

/-- The `Z` contribution to any finite switched set is at most one. -/
theorem card_zIn_le_one
    (K : Finset (Switching.Vertex V k s)) :
    Fintype.card (ZIn K) ≤ 1 := by
  let f : ZIn K ↪ Unit :=
    ⟨Subtype.val, Subtype.val_injective⟩
  simpa using Fintype.card_le_of_injective f f.injective

end SecondConnector
end RamseyIncrement
