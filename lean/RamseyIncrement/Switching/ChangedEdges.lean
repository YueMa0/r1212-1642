/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Construction

/-!
# The edges changed by the final switching

This file records the source colors of all switches in (9)--(10), gives
orientation-independent descriptions of the two switch graphs, and reduces
any forbidden clique in the final graph to one of the dangerous rows in
(11).
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- The unordered pair with endpoints `a` and `b`. -/
def SymmPair {α : Type*} (a b u v : α) : Prop :=
  (u = a ∧ v = b) ∨ (u = b ∧ v = a)

theorem symmPair_comm {α : Type*} (a b u v : α) :
    SymmPair a b u v ↔ SymmPair a b v u := by
  simp only [SymmPair]
  aesop

theorem symmPair_swap {α : Type*} (a b u v : α) :
    SymmPair a b u v ↔ SymmPair b a u v := by
  simp only [SymmPair]
  aesop

theorem Vertex.c0_ne_c2
    (cert : Certificates.OrderedCertificates G k s) :
    Vertex.c0 cert ≠ Vertex.c2 cert := by
  intro h
  have hval := congrArg Fin.val h
  simp [Vertex.c0, Vertex.c2, Certificates.c0Index] at hval

private theorem fromRel_adj_iff_symmetrize
    {α : Type*} (R : α → α → Prop)
    (hne : ∀ ⦃u v⦄, R u v → u ≠ v) (u v : α) :
    (SimpleGraph.fromRel R).Adj u v ↔ R u v ∨ R v u := by
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    constructor
    · rcases h with huv | hvu
      · exact hne huv
      · exact (hne hvu).symm
    · exact h

private theorem addedRedRel_ne
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s} (h : addedRedRel cert u v) :
    u ≠ v := by
  rcases h with h | h | h
  · obtain ⟨q, _, rfl, rfl⟩ := h
    simp
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rcases h with ⟨rfl, rfl⟩
    simpa using Vertex.c0_ne_c2 cert

private theorem removedRedRel_ne
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s} (h : removedRedRel cert u v) :
    u ≠ v := by
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨q, _, rfl, rfl⟩ := h
    simp
  · rcases h with ⟨rfl, rfl⟩
    simp
  · rcases h with ⟨rfl, rfl⟩
    simp
  · obtain ⟨q, _, rfl, rfl⟩ := h
    simp
  · obtain ⟨q, _, rfl, rfl⟩ := h
    simp
  · rcases h with ⟨_, rfl, rfl⟩
    simp
  · obtain ⟨q, _, hq2, rfl, rfl⟩ := h
    intro heq
    have hindex : Vertex.i1 cert = q := by
      simpa [Vertex.y] using heq
    have hval := congrArg Fin.val hindex
    simp [Vertex.i1, Certificates.i1Index'] at hval
    omega

/-- Exact, orientation-independent classification of the edges changed
from blue to red. -/
@[simp]
theorem addedRedGraph_adj_iff
    (cert : Certificates.OrderedCertificates G k s)
    (u v : Vertex V k s) :
    (addedRedGraph cert).Adj u v ↔
      (∃ q ∈ cert.T,
        SymmPair (Vertex.a (Vertex.c0 cert))
          (Vertex.y cert (some q)) u v) ∨
      SymmPair (Vertex.b (Vertex.c0 cert))
        (Vertex.y cert none) u v ∨
      SymmPair (Vertex.b (Vertex.c0 cert))
        (Vertex.b (Vertex.c2 cert)) u v := by
  simp only [addedRedGraph, SimpleGraph.fromRel_adj, addedRedRel]
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with h | h | h
      · obtain ⟨q, hq, rfl, rfl⟩ := h
        exact Or.inl ⟨q, hq, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases h with h | h | h
      · obtain ⟨q, hq, rfl, rfl⟩ := h
        exact Or.inl ⟨q, hq, Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inr (Or.inl (Or.inr ⟨h.2, h.1⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
  · intro h
    rcases h with h | h | h
    · obtain ⟨q, hq, h | h⟩ := h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp, Or.inl (Or.inl ⟨q, hq, rfl, rfl⟩)⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp, Or.inr (Or.inl ⟨q, hq, rfl, rfl⟩)⟩
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp, Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simp, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simpa using Vertex.c0_ne_c2 cert,
          Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨by simpa using (Vertex.c0_ne_c2 cert).symm,
          Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- Exact, orientation-independent classification of the edges changed
from red to blue. -/
@[simp]
theorem removedRedGraph_adj_iff
    (cert : Certificates.OrderedCertificates G k s)
    (u v : Vertex V k s) :
    (removedRedGraph cert).Adj u v ↔
      (∃ q ∈ cert.T,
        SymmPair (Vertex.b (Vertex.c0 cert))
          (Vertex.y cert (some q)) u v) ∨
      SymmPair (Vertex.b (Vertex.c0 cert))
        (Vertex.x cert (some (Vertex.i1 cert))) u v ∨
      SymmPair (Vertex.b (Vertex.c0 cert))
        (Vertex.x cert none) u v ∨
      (∃ q, q ≠ Vertex.i1 cert ∧
        SymmPair Vertex.z (Vertex.x cert (some q)) u v) ∨
      (∃ q ∈ cert.E,
        SymmPair (Vertex.a (Vertex.c0 cert))
          (Vertex.x cert (some q)) u v) ∨
      (cert.E.Nonempty ∧
        SymmPair (Vertex.y cert (some (Vertex.i1 cert)))
          (Vertex.y cert none) u v) ∨
      (∃ q ∈ cert.E, 2 ≤ q.val ∧
        SymmPair (Vertex.y cert (some (Vertex.i1 cert)))
          (Vertex.y cert (some q)) u v) := by
  have hne :
      ∀ ⦃u v : Vertex V k s⦄, removedRedRel cert u v → u ≠ v :=
    fun {_ _} h ↦ removedRedRel_ne cert h
  rw [removedRedGraph,
    fromRel_adj_iff_symmetrize (removedRedRel cert) hne]
  constructor
  · rintro (h | h)
    · rcases h with h | h | h | h | h | h | h
      · obtain ⟨q, hq, hu, hv⟩ := h
        left
        exact ⟨q, hq, Or.inl ⟨hu, hv⟩⟩
      · right
        left
        exact Or.inl h
      · right
        right
        left
        exact Or.inl h
      · obtain ⟨q, hq, hu, hv⟩ := h
        right
        right
        right
        left
        exact ⟨q, hq, Or.inl ⟨hu, hv⟩⟩
      · obtain ⟨q, hq, hu, hv⟩ := h
        right
        right
        right
        right
        left
        exact ⟨q, hq, Or.inl ⟨hu, hv⟩⟩
      · obtain ⟨hE, hu, hv⟩ := h
        right
        right
        right
        right
        right
        left
        exact ⟨hE, Or.inl ⟨hu, hv⟩⟩
      · obtain ⟨q, hq, hq2, hu, hv⟩ := h
        right
        right
        right
        right
        right
        right
        exact ⟨q, hq, hq2, Or.inl ⟨hu, hv⟩⟩
    · rcases h with h | h | h | h | h | h | h
      · obtain ⟨q, hq, hv, hu⟩ := h
        left
        exact ⟨q, hq, Or.inr ⟨hu, hv⟩⟩
      · right
        left
        exact Or.inr ⟨h.2, h.1⟩
      · right
        right
        left
        exact Or.inr ⟨h.2, h.1⟩
      · obtain ⟨q, hq, hv, hu⟩ := h
        right
        right
        right
        left
        exact ⟨q, hq, Or.inr ⟨hu, hv⟩⟩
      · obtain ⟨q, hq, hv, hu⟩ := h
        right
        right
        right
        right
        left
        exact ⟨q, hq, Or.inr ⟨hu, hv⟩⟩
      · obtain ⟨hE, hv, hu⟩ := h
        right
        right
        right
        right
        right
        left
        exact ⟨hE, Or.inr ⟨hu, hv⟩⟩
      · obtain ⟨q, hq, hq2, hv, hu⟩ := h
        right
        right
        right
        right
        right
        right
        exact ⟨q, hq, hq2, Or.inr ⟨hu, hv⟩⟩
  · intro h
    rcases h with h | h | h | h | h | h | h
    · obtain ⟨q, hq, h | h⟩ := h
      · left
        left
        exact ⟨q, hq, h.1, h.2⟩
      · right
        left
        exact ⟨q, hq, h.2, h.1⟩
    · rcases h with h | h
      · left
        right
        left
        exact h
      · right
        right
        left
        exact ⟨h.2, h.1⟩
    · rcases h with h | h
      · left
        right
        right
        left
        exact h
      · right
        right
        right
        left
        exact ⟨h.2, h.1⟩
    · obtain ⟨q, hq, h | h⟩ := h
      · left
        right
        right
        right
        left
        exact ⟨q, hq, h.1, h.2⟩
      · right
        right
        right
        right
        left
        exact ⟨q, hq, h.2, h.1⟩
    · obtain ⟨q, hq, h | h⟩ := h
      · left
        right
        right
        right
        right
        left
        exact ⟨q, hq, h.1, h.2⟩
      · right
        right
        right
        right
        right
        left
        exact ⟨q, hq, h.2, h.1⟩
    · obtain ⟨hE, h | h⟩ := h
      · left
        right
        right
        right
        right
        right
        left
        exact ⟨hE, h.1, h.2⟩
      · right
        right
        right
        right
        right
        right
        left
        exact ⟨hE, h.2, h.1⟩
    · obtain ⟨q, hq, hq2, h | h⟩ := h
      · left
        right
        right
        right
        right
        right
        right
        exact ⟨q, hq, hq2, h.1, h.2⟩
      · right
        right
        right
        right
        right
        right
        right
        exact ⟨q, hq, hq2, h.2, h.1⟩

@[simp]
theorem addedRedGraph_adj_a0_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (addedRedGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
        q ∈ cert.T := by
  simp [SymmPair]

@[simp]
theorem addedRedGraph_adj_y_a0_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (addedRedGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.a (Vertex.c0 cert)) ↔
        q ∈ cert.T := by
  rw [(addedRedGraph cert).adj_comm]
  exact addedRedGraph_adj_a0_y_iff cert q

@[simp]
theorem addedRedGraph_adj_b0_yStar
    (cert : Certificates.OrderedCertificates G k s) :
    (addedRedGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.y cert none) := by
  simp [SymmPair]

@[simp]
theorem addedRedGraph_adj_yStar_b0
    (cert : Certificates.OrderedCertificates G k s) :
    (addedRedGraph cert).Adj
      (Vertex.y cert none) (Vertex.b (Vertex.c0 cert)) :=
  (addedRedGraph cert).adj_symm (addedRedGraph_adj_b0_yStar cert)

@[simp]
theorem addedRedGraph_adj_b0_b2
    (cert : Certificates.OrderedCertificates G k s) :
    (addedRedGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.b (Vertex.c2 cert)) := by
  simp [SymmPair, Vertex.c0_ne_c2 cert]

@[simp]
theorem addedRedGraph_adj_b2_b0
    (cert : Certificates.OrderedCertificates G k s) :
    (addedRedGraph cert).Adj
      (Vertex.b (Vertex.c2 cert)) (Vertex.b (Vertex.c0 cert)) :=
  (addedRedGraph cert).adj_symm (addedRedGraph_adj_b0_b2 cert)

@[simp]
theorem removedRedGraph_adj_b0_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
        q ∈ cert.T := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_y_b0_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some q)) (Vertex.b (Vertex.c0 cert)) ↔
        q ∈ cert.T := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_adj_b0_y_iff cert q

@[simp]
theorem removedRedGraph_adj_b0_x1
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.x cert (some (Vertex.i1 cert))) := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_x1_b0
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.x cert (some (Vertex.i1 cert)))
      (Vertex.b (Vertex.c0 cert)) :=
  (removedRedGraph cert).adj_symm (removedRedGraph_adj_b0_x1 cert)

@[simp]
theorem removedRedGraph_adj_b0_xStar
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.x cert none) := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_xStar_b0
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.x cert none) (Vertex.b (Vertex.c0 cert)) :=
  (removedRedGraph cert).adj_symm (removedRedGraph_adj_b0_xStar cert)

@[simp]
theorem removedRedGraph_adj_a0_x_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert (some q)) ↔
        q ∈ cert.E := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_x_a0_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj
      (Vertex.x cert (some q)) (Vertex.a (Vertex.c0 cert)) ↔
        q ∈ cert.E := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_adj_a0_x_iff cert q

@[simp]
theorem removedRedGraph_adj_z_x_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj Vertex.z (Vertex.x cert (some q)) ↔
      q ≠ Vertex.i1 cert := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_x_z_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (removedRedGraph cert).Adj (Vertex.x cert (some q)) Vertex.z ↔
      q ≠ Vertex.i1 cert := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_adj_z_x_iff cert q

@[simp]
theorem removedRedGraph_not_adj_z_xStar
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(removedRedGraph cert).Adj Vertex.z (Vertex.x cert none) := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_not_adj_xStar_z
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(removedRedGraph cert).Adj (Vertex.x cert none) Vertex.z := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_not_adj_z_xStar cert

@[simp]
theorem removedRedGraph_adj_y1_yStar_iff
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert none) ↔ cert.E.Nonempty := by
  simp [SymmPair]

@[simp]
theorem removedRedGraph_adj_yStar_y1_iff
    (cert : Certificates.OrderedCertificates G k s) :
    (removedRedGraph cert).Adj
      (Vertex.y cert none)
      (Vertex.y cert (some (Vertex.i1 cert))) ↔ cert.E.Nonempty := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_adj_y1_yStar_iff cert

@[simp]
theorem removedRedGraph_adj_y1_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (hq : 2 ≤ q.val) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert (some q)) ↔ q ∈ cert.E := by
  simp [SymmPair]
  constructor
  · rintro ⟨r, hr, _, h | h⟩
    · simpa [h] using hr
    · have hval := congrArg Fin.val h.2
      have hi1val : (Vertex.i1 cert).val = 1 := rfl
      rw [hi1val] at hval
      omega
  · intro h
    exact ⟨q, h, hq, Or.inl rfl⟩

@[simp]
theorem removedRedGraph_adj_y_y1_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (hq : 2 ≤ q.val) :
    (removedRedGraph cert).Adj
      (Vertex.y cert (some q))
      (Vertex.y cert (some (Vertex.i1 cert))) ↔ q ∈ cert.E := by
  rw [(removedRedGraph cert).adj_comm]
  exact removedRedGraph_adj_y1_y_iff cert q hq

/-- The graph before cloning is the Ramsey-free graph supplied by the two
canonical special lifts. -/
theorem canonicalGraph_isRamseyFree
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (canonicalGraph cert) (k + 1) (s + 1) := by
  simpa [canonicalGraph] using
    Canonical.graph_isRamseyFree cert.toCertificates cert.five_le_k
      cert.five_le_s hG

/-- Adding the red-joined clone creates no blue `K_(s+1)`. -/
theorem preGraph_compl_cliqueFree
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    (preGraph cert)ᶜ.CliqueFree (s + 1) := by
  classical
  exact redJoinedClone.compl_cliqueFree
    (canonicalGraph_isRamseyFree cert hG).2

/-- Every red `K_(k+1)` before switching contains both `b₀` and `z`. -/
theorem preGraph_red_clique_contains_b0_z
    [DecidableEq V]
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    {t : Finset (Vertex V k s)}
    (ht : (preGraph cert).IsNClique (k + 1) t) :
    Vertex.b (Vertex.c0 cert) ∈ t ∧ Vertex.z ∈ t := by
  exact redJoinedClone.red_clique_contains_source_and_clone
    (canonicalGraph_isRamseyFree cert hG).1 ht

@[simp]
theorem outerIndexEquiv_apply_symm
    {s : ℕ} (h₁ h₂ : 1 ≤ s) (r : Option (Fin (s - 1))) :
    Canonical.outerIndexEquiv h₁
        ((Canonical.outerIndexEquiv h₂).symm r) = r := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  exact Equiv.apply_symm_apply _ _

@[simp]
theorem outerIndexEquiv_symm_some_val
    {s : ℕ} (hs : 1 ≤ s) (q : Fin (s - 1)) :
    ((Canonical.outerIndexEquiv hs).symm (some q)).val = q.val := by
  simp [Canonical.outerIndexEquiv]

@[simp]
theorem outerIndexEquiv_symm_none_val
    {s : ℕ} (hs : 1 ≤ s) :
    ((Canonical.outerIndexEquiv hs).symm none).val = s - 1 := by
  simp [Canonical.outerIndexEquiv]

@[simp]
theorem secondCertificate_symm_apply
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm r) =
      Canonical.secondCertificateAt cert.toCertificates cert.five_le_k r := by
  rw [Canonical.secondCertificate_apply]
  simp

namespace Vertex

/-- Inclusion of an arbitrary first-lift vertex into the lower block of
the canonical graph and then into the clone graph. -/
abbrev lower (w : SpecialLiftVertex V k) : Vertex V k s :=
  .inl (.core w)

end Vertex

/-- Edges between two lower vertices retain their color from the first
special lift. -/
@[simp]
theorem preGraph_adj_lower_lower_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w v : SpecialLiftVertex V k) :
    (preGraph cert).Adj (Vertex.lower w) (Vertex.lower v) ↔
      (specialLift G cert.c).Adj w v := by
  change (canonicalGraph cert).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.core (k := Nat.succ s) v) ↔
      (specialLift G cert.c).Adj w v
  change ((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.core (k := Nat.succ s) v) ↔
      (specialLift G cert.c).Adj w v
  simp
  constructor
  · rintro ⟨hne, hadj⟩
    exact hadj hne
  · intro hadj
    exact ⟨hadj.ne, fun _ ↦ hadj⟩

/-- The general source-color rule between a lower vertex and an `X`
vertex. -/
@[simp]
theorem preGraph_adj_lower_x_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w : SpecialLiftVertex V k) (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj (Vertex.lower w) (Vertex.x cert r) ↔
      Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r ≠ w := by
  change (canonicalGraph cert).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r)) ↔
      Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r ≠ w
  change ((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r)) ↔
      Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r ≠ w
  rw [specialLift_compl_adj_core_a]
  simp only [Nat.succ_sub_one]
  with_unfolding_all
    change Canonical.secondCertificateAt cert.toCertificates
      cert.five_le_k
      (Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm r)) ≠ w ↔
      Canonical.secondCertificateAt cert.toCertificates
        cert.five_le_k r ≠ w
  rw [outerIndexEquiv_apply_symm]

/-- The general source-color rule between a lower vertex and a `Y`
vertex. -/
@[simp]
theorem preGraph_adj_lower_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (w : SpecialLiftVertex V k) (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj (Vertex.lower w) (Vertex.y cert r) ↔
      w = Canonical.secondCertificateAt cert.toCertificates
          cert.five_le_k r ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificateAt cert.toCertificates
            cert.five_le_k r) w := by
  change (canonicalGraph cert).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r)) ↔
      w = Canonical.secondCertificateAt cert.toCertificates
          cert.five_le_k r ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificateAt cert.toCertificates
            cert.five_le_k r) w
  change ((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.core (k := Nat.succ s) w)
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r)) ↔
      w = Canonical.secondCertificateAt cert.toCertificates
          cert.five_le_k r ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificateAt cert.toCertificates
            cert.five_le_k r) w
  rw [specialLift_compl_adj_core_b]
  simp only [Nat.succ_sub_one]
  with_unfolding_all
    change w =
        Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
          (Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              cert.five_le_s)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                cert.five_le_s)).symm r)) ∨
      (specialLift G cert.c)ᶜᶜ.Adj
        (Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
          (Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              cert.five_le_s)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                cert.five_le_s)).symm r)))
        w ↔
      (w = Canonical.secondCertificateAt cert.toCertificates
          cert.five_le_k r ∨
        (specialLift G cert.c).Adj
          (Canonical.secondCertificateAt cert.toCertificates
            cert.five_le_k r) w)
  rw [outerIndexEquiv_apply_symm]
  simp

/-- The source-color rule inside `Y`: the two ordinary outer parts are
blue, and their cross edges are red. -/
@[simp]
theorem preGraph_adj_y_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (preGraph cert).Adj (Vertex.y cert r) (Vertex.y cert t) ↔
      (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm r ≠
        (Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm t ∧
      ¬SameBPart (k := Nat.succ s)
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm r)
        ((Canonical.outerIndexEquiv
          (le_trans (by decide : 1 ≤ 5)
            cert.five_le_s)).symm t) := by
  change (canonicalGraph cert).Adj
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t)) ↔ _
  change ((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t)) ↔ _
  rw [specialLift_compl_adj_b_b]
  exact ⟨id, id⟩

/-- `X` is blue-complete before switching. -/
theorem preGraph_not_adj_x_x
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    ¬(preGraph cert).Adj (Vertex.x cert r) (Vertex.x cert t) := by
  change ¬(canonicalGraph cert).Adj
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t))
  change ¬((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t))
  simp

/-- Before switching, `x_r y_t` is red exactly for the matched pair. -/
@[simp]
theorem preGraph_adj_x_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (r t : Option (Fin (s - 1))) :
    (preGraph cert).Adj (Vertex.x cert r) (Vertex.y cert t) ↔ r = t := by
  change (canonicalGraph cert).Adj
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t)) ↔ r = t
  change ((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.a (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm t)) ↔ r = t
  rw [specialLift_compl_adj_a_b]
  exact (Canonical.outerIndexEquiv _).symm.injective.eq_iff

/-- Source color for the first family in (9)(i). -/
theorem preGraph_not_adj_a0_y
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    ¬(preGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)) := by
  change ¬(canonicalGraph cert).Adj
    (SpecialLiftVertex.core (k := Nat.succ s)
      (SpecialLiftVertex.a (V := V) (Vertex.c0 cert)))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)).symm (some q)))
  change ¬((specialLift (k := Nat.succ s) (specialLift G cert.c)ᶜ
    (Canonical.secondCertificate (s := s) cert.toCertificates cert.five_le_k
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)))ᶜ).Adj
    (SpecialLiftVertex.core (k := Nat.succ s)
      (SpecialLiftVertex.a (V := V) (Vertex.c0 cert)))
    (SpecialLiftVertex.b (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
      (le_trans (by decide : 1 ≤ 5)
        cert.five_le_s)).symm (some q)))
  rw [specialLift_compl_adj_core_b]
  simp only [Nat.succ_sub_one]
  with_unfolding_all
    change ¬(SpecialLiftVertex.a (V := V) (Vertex.c0 cert) =
        Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
          (Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              cert.five_le_s)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                cert.five_le_s)).symm (some q))) ∨
      (specialLift G cert.c)ᶜᶜ.Adj
        (Canonical.secondCertificateAt cert.toCertificates cert.five_le_k
          (Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              cert.five_le_s)
            ((Canonical.outerIndexEquiv
              (le_trans (by decide : 1 ≤ 5)
                cert.five_le_s)).symm (some q))))
        (SpecialLiftVertex.a (V := V) (Vertex.c0 cert)))
  rw [outerIndexEquiv_apply_symm]
  simp [Canonical.secondCertificateAt, Vertex.c0, cert.c_ne_i]

/-- The clone `b₀` has the color of `c₀i_q`; for `q ∈ T` this is the
red source color in (9)(i). -/
@[simp]
theorem preGraph_adj_b0_y_iff
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)) ↔
        q ∈ cert.T := by
  have hne :
      cert.i q ≠ cert.c (Certificates.c0Index cert.five_le_k) :=
    (cert.c_ne_i (Certificates.c0Index cert.five_le_k) q).symm
  rw [preGraph_adj_lower_y_iff]
  simp [Canonical.secondCertificateAt, Vertex.c0, cert.mem_T,
    hne]

/-- Source color of `b₀y_*` in (9)(ii). -/
theorem preGraph_not_adj_b0_yStar
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.y cert none) := by
  rw [preGraph_adj_lower_y_iff]
  simp [Canonical.secondCertificateAt]

/-- Source color of `b₀b₂` in (9)(ii). -/
theorem preGraph_not_adj_b0_b2
    (cert : Certificates.OrderedCertificates G k s) :
    ¬(preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.b (Vertex.c2 cert)) := by
  rw [preGraph_adj_lower_lower_iff]
  simp [SameBPart, Vertex.c0, Vertex.c2, Certificates.c0Index]

/-- Source color of `b₀x₁` in (9)(iii). -/
theorem preGraph_adj_b0_x1
    (cert : Certificates.OrderedCertificates G k s) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert))
      (Vertex.x cert (some (Vertex.i1 cert))) := by
  rw [preGraph_adj_lower_x_iff]
  simp [Canonical.secondCertificateAt]

/-- Source color of `b₀x_*` in (9)(iii). -/
theorem preGraph_adj_b0_xStar
    (cert : Certificates.OrderedCertificates G k s) :
    (preGraph cert).Adj
      (Vertex.b (Vertex.c0 cert)) (Vertex.x cert none) := by
  rw [preGraph_adj_lower_x_iff]
  simp [Canonical.secondCertificateAt]

/-- Source color of the `a₀x_q` switches in (10). -/
theorem preGraph_adj_a0_x
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) :
    (preGraph cert).Adj
      (Vertex.a (Vertex.c0 cert)) (Vertex.x cert (some q)) := by
  rw [preGraph_adj_lower_x_iff]
  simp [Canonical.secondCertificateAt]

/-- Before switching, `z` copies the red `b₀x_r` color for every
ordinary or starred index. -/
theorem preGraph_adj_z_x
    (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) :
    (preGraph cert).Adj Vertex.z (Vertex.x cert r) := by
  change (redJoinedClone (canonicalGraph cert)
    (SpecialLiftVertex.core (k := Nat.succ s)
      (SpecialLiftVertex.b (Vertex.c0 cert)))).Adj
    CloneVertex.z
    (.inl (SpecialLiftVertex.a
      (V := SpecialLiftVertex V k) (k := Nat.succ s)
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm r)))
  rw [redJoinedClone.adj_z_old]
  right
  have hpre :
      (preGraph cert).Adj
        (Vertex.b (Vertex.c0 cert)) (Vertex.x cert r) :=
    (preGraph_adj_lower_x_iff cert
      (SpecialLiftVertex.b (Vertex.c0 cert)) r).2 (by
        cases r <;> simp [Canonical.secondCertificateAt])
  simpa [preGraph] using hpre

/-- Source color of the exceptional `y₁y_*` switch in (10). -/
theorem preGraph_adj_y1_yStar
    (cert : Certificates.OrderedCertificates G k s) :
    (preGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert none) := by
  rw [preGraph_adj_y_y_iff]
  have hi :
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm
        (some (Vertex.i1 cert))).val = 1 := by
    rw [outerIndexEquiv_symm_some_val]
    rfl
  have hstar :
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm none).val =
        s - 1 :=
    outerIndexEquiv_symm_none_val _
  have hs5 : 5 ≤ s := cert.five_le_s
  constructor
  · intro h
    have hval := congrArg Fin.val h
    rw [hi, hstar] at hval
    omega
  · intro hpart
    rcases hpart with hsmall | hlarge
    · have h := hsmall.2
      rw [hstar] at h
      omega
    · have h := hlarge.1
      rw [hi] at h
      omega

/-- Source color of the exceptional large `y₁y_q` switches in (10). -/
theorem preGraph_adj_y1_y_of_two_le
    (cert : Certificates.OrderedCertificates G k s)
    (q : Fin (s - 1)) (hq : 2 ≤ q.val) :
    (preGraph cert).Adj
      (Vertex.y cert (some (Vertex.i1 cert)))
      (Vertex.y cert (some q)) := by
  rw [preGraph_adj_y_y_iff]
  have hi :
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm
        (some (Vertex.i1 cert))).val = 1 := by
    rw [outerIndexEquiv_symm_some_val]
    rfl
  have hqval :
      ((Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5)
          cert.five_le_s)).symm (some q)).val =
        q.val :=
    outerIndexEquiv_symm_some_val _ q
  constructor
  · intro h
    have hval := congrArg Fin.val h
    rw [hi, hqval] at hval
    omega
  · intro hpart
    rcases hpart with hsmall | hlarge
    · have h := hsmall.2
      rw [hqval] at h
      omega
    · have h := hlarge.1
      rw [hi] at h
      omega

/-- Every listed blue-to-red switch really has blue source color. -/
theorem addedRedGraph_source_blue
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (h : (addedRedGraph cert).Adj u v) :
    ¬(preGraph cert).Adj u v := by
  rw [addedRedGraph_adj_iff] at h
  rcases h with h | h | h
  · obtain ⟨q, _, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_not_adj_a0_y cert q
    · rcases h with ⟨rfl, rfl⟩
      intro hadj
      exact preGraph_not_adj_a0_y cert q
        ((preGraph cert).adj_symm hadj)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_not_adj_b0_yStar cert
    · rcases h with ⟨rfl, rfl⟩
      intro hadj
      exact preGraph_not_adj_b0_yStar cert
        ((preGraph cert).adj_symm hadj)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_not_adj_b0_b2 cert
    · rcases h with ⟨rfl, rfl⟩
      intro hadj
      exact preGraph_not_adj_b0_b2 cert
        ((preGraph cert).adj_symm hadj)

/-- The newly-red graph is a subgraph of the old blue graph. -/
theorem addedRedGraph_le_preGraph_compl
    (cert : Certificates.OrderedCertificates G k s) :
    addedRedGraph cert ≤ (preGraph cert)ᶜ := by
  intro u v h
  exact (SimpleGraph.compl_adj _ _ _).2
    ⟨h.ne, addedRedGraph_source_blue cert h⟩

/-- Every listed red-to-blue switch really has red source color. -/
theorem removedRedGraph_source_red
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (h : (removedRedGraph cert).Adj u v) :
    (preGraph cert).Adj u v := by
  rw [removedRedGraph_adj_iff] at h
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨q, hq, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph_adj_b0_y_iff cert q).2 hq
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm
        ((preGraph_adj_b0_y_iff cert q).2 hq)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_b0_x1 cert
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm (preGraph_adj_b0_x1 cert)
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_b0_xStar cert
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm (preGraph_adj_b0_xStar cert)
  · obtain ⟨q, _, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_z_x cert (some q)
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm (preGraph_adj_z_x cert (some q))
  · obtain ⟨q, _, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_a0_x cert q
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm (preGraph_adj_a0_x cert q)
  · obtain ⟨_, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_y1_yStar cert
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm (preGraph_adj_y1_yStar cert)
  · obtain ⟨q, _, hq2, h | h⟩ := h
    · rcases h with ⟨rfl, rfl⟩
      exact preGraph_adj_y1_y_of_two_le cert q hq2
    · rcases h with ⟨rfl, rfl⟩
      exact (preGraph cert).adj_symm
        (preGraph_adj_y1_y_of_two_le cert q hq2)

/-- The recolored-blue graph is a subgraph of the old red graph. -/
theorem removedRedGraph_le_preGraph
    (cert : Certificates.OrderedCertificates G k s) :
    removedRedGraph cert ≤ preGraph cert := by
  intro u v h
  exact removedRedGraph_source_red cert h

end Switching
end RamseyIncrement
