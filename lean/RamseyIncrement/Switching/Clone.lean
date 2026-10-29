/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Basic

/-!
# The red-joined clone

This is the intermediate graph obtained by adjoining `z` as a clone of a
source vertex `b`, except that the edge `bz` is red.
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

/-- Old vertices together with one new clone vertex. -/
abbrev CloneVertex (V : Type*) := V ⊕ Unit

namespace CloneVertex

variable {V : Type*}

/-- Inclusion of an old vertex. -/
abbrev old (v : V) : CloneVertex V := Sum.inl v

/-- The new clone vertex. -/
abbrev z : CloneVertex V := Sum.inr ()

/-- Collapse the clone onto its source. -/
def collapse (b : V) : CloneVertex V → V
  | .inl v => v
  | .inr _ => b

end CloneVertex

/-- Add a clone of `b`, joining the source to its clone in red. -/
def redJoinedClone {V : Type*} (G : SimpleGraph V) (b : V) :
    SimpleGraph (CloneVertex V) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr _ => u = b ∨ G.Adj u b
    | .inr _, .inl v => v = b ∨ G.Adj b v
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro u v
    cases u <;> cases v <;> simp only
    · intro h
      exact G.adj_symm h
    · intro h
      exact h.imp id G.adj_symm
    · intro h
      exact h.imp id G.adj_symm
    · intro h
      exact h.elim
  loopless := by
    constructor
    intro u
    cases u with
    | inl u => exact G.loopless.irrefl u
    | inr _ => exact id

namespace redJoinedClone

variable {V : Type*} (G : SimpleGraph V) (b u v : V)

@[simp]
theorem adj_old_old :
    (redJoinedClone G b).Adj (.inl u) (.inl v) ↔ G.Adj u v :=
  Iff.rfl

@[simp]
theorem adj_old_z :
    (redJoinedClone G b).Adj (.inl u) CloneVertex.z ↔
      u = b ∨ G.Adj u b :=
  Iff.rfl

@[simp]
theorem adj_z_old :
    (redJoinedClone G b).Adj CloneVertex.z (.inl u) ↔
      u = b ∨ G.Adj b u :=
  Iff.rfl

@[simp]
theorem not_adj_z_z :
    ¬(redJoinedClone G b).Adj CloneVertex.z CloneVertex.z :=
  id

end redJoinedClone

@[simp]
theorem card_cloneVertex [Fintype V] :
    Fintype.card (CloneVertex V) = Fintype.card V + 1 := by
  simp [CloneVertex]

namespace redJoinedClone

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V} {b : V} {n : ℕ} {t : Finset (CloneVertex V)}

private theorem collapse_injOn
    (hpair : ¬(.inl b ∈ t ∧ CloneVertex.z ∈ t)) :
    Set.InjOn (CloneVertex.collapse b) t := by
  intro x hx y hy hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => simpa [CloneVertex.collapse] using hxy
      | inr _ =>
          simp only [CloneVertex.collapse] at hxy
          subst x
          exact False.elim (hpair ⟨hx, hy⟩)
  | inr _ =>
      cases y with
      | inl y =>
          simp only [CloneVertex.collapse] at hxy
          subst y
          exact False.elim (hpair ⟨hy, hx⟩)
      | inr _ => rfl

private theorem collapse_maps_clique
    (hpair : ¬(.inl b ∈ t ∧ CloneVertex.z ∈ t))
    (ht : (redJoinedClone G b).IsClique t) :
    G.IsClique (t.image (CloneVertex.collapse b)) := by
  intro x hx y hy hxy
  obtain ⟨x', hx't, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y', hy't, rfl⟩ := Finset.mem_image.mp hy
  have hx'y' : x' ≠ y' := by
    intro h
    subst y'
    exact hxy rfl
  have hadj := ht hx't hy't hx'y'
  cases x' with
  | inl x =>
      cases y' with
      | inl y => exact hadj
      | inr _ =>
          simp only [redJoinedClone, CloneVertex.collapse] at hadj ⊢
          exact hadj.resolve_left (by
            intro hxb
            subst x
            exact hpair ⟨hx't, hy't⟩)
  | inr _ =>
      cases y' with
      | inl y =>
          simp only [redJoinedClone, CloneVertex.collapse] at hadj ⊢
          exact hadj.resolve_left (by
            intro hyb
            subst y
            exact hpair ⟨hy't, hx't⟩)
      | inr _ => exact False.elim (hx'y' rfl)

/-- A blue clique in the red-joined clone collapses injectively to a blue
clique in the old graph. -/
private theorem collapse_maps_compl_clique
    (ht : (redJoinedClone G b)ᶜ.IsClique t) :
    Gᶜ.IsClique (t.image (CloneVertex.collapse b)) := by
  have hpair : ¬(.inl b ∈ t ∧ CloneVertex.z ∈ t) := by
    rintro ⟨hb, hz⟩
    have hadj := ht hb hz (by simp)
    simpa [redJoinedClone] using hadj
  intro x hx y hy hxy
  obtain ⟨x', hx't, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y', hy't, rfl⟩ := Finset.mem_image.mp hy
  have hx'y' : x' ≠ y' := by
    intro h
    subst y'
    exact hxy rfl
  have hadj := ht hx't hy't hx'y'
  cases x' with
  | inl x =>
      cases y' with
      | inl y => simpa [CloneVertex.collapse] using hadj
      | inr _ =>
          simpa [redJoinedClone, CloneVertex.collapse] using hadj
  | inr _ =>
      cases y' with
      | inl y =>
          simp [redJoinedClone, CloneVertex.collapse] at hadj
          exact (SimpleGraph.compl_adj G b y).2
            ⟨Ne.symm hadj.1, hadj.2⟩
      | inr _ => exact False.elim (hx'y' rfl)

/-- Every red `n`-clique in the red-joined clone of an `n`-clique-free
graph contains both the source and the new clone. -/
theorem red_clique_contains_source_and_clone
    (hG : G.CliqueFree n)
    (ht : (redJoinedClone G b).IsNClique n t) :
    .inl b ∈ t ∧ CloneVertex.z ∈ t := by
  by_contra hpair
  apply hG (t.image (CloneVertex.collapse b))
  constructor
  · exact collapse_maps_clique hpair ht.isClique
  · rw [Finset.card_image_of_injOn (collapse_injOn hpair), ht.card_eq]

/-- Red-joining the source to its clone cannot create a new blue clique. -/
theorem compl_cliqueFree
    (hG : Gᶜ.CliqueFree n) :
    (redJoinedClone G b)ᶜ.CliqueFree n := by
  intro t ht
  have hpair : ¬(.inl b ∈ t ∧ CloneVertex.z ∈ t) := by
    rintro ⟨hb, hz⟩
    have hadj := ht.isClique hb hz (by simp)
    simpa [redJoinedClone] using hadj
  apply hG (t.image (CloneVertex.collapse b))
  constructor
  · exact collapse_maps_compl_clique ht.isClique
  · rw [Finset.card_image_of_injOn (collapse_injOn hpair), ht.card_eq]

end redJoinedClone
end Switching
end RamseyIncrement
