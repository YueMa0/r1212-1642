/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Basic

/-!
# Projection tools for local clique bounds

Many second-connector cases replace a few tagged vertices by core vertices.
The replacement map need not be globally injective: it only has to be
injective on the clique under consideration.  These lemmas package that
recurring `Set.InjOn` argument.
-/

namespace RamseyIncrement
namespace SecondConnector

open Finset
open SimpleGraph

universe u v

variable {α : Type u} {β : Type v}

/-- An adjacency-preserving map sends a finite clique to a clique.  Global
injectivity is not required for this statement; distinct image vertices
already have distinct preimages. -/
theorem isClique_image_of_mapsAdj
    [DecidableEq β]
    {G : SimpleGraph α} {H : SimpleGraph β}
    (K : Finset α) (f : α → β)
    (hK : G.IsClique K)
    (hadj :
      ∀ ⦃x y⦄, x ∈ K → y ∈ K →
        G.Adj x y → H.Adj (f x) (f y)) :
    H.IsClique (K.image f) := by
  classical
  intro _ hfx _ hfy hne
  obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hfx
  obtain ⟨y, hyK, rfl⟩ := Finset.mem_image.mp hfy
  exact hadj hxK hyK
    (hK hxK hyK (fun hxy ↦ hne (congrArg f hxy)))

/-- A map injective on a set, carrying that set into a clique-free target
set and preserving adjacency there, pulls clique-freeness back to the
source set. -/
theorem cliqueFreeOn_of_injOn_projection
    {G : SimpleGraph α} {H : SimpleGraph β}
    {S : Set α} {T : Set β} {n : ℕ}
    (f : α → β)
    (hinj : Set.InjOn f S)
    (hmap : Set.MapsTo f S T)
    (hadj :
      ∀ ⦃x y⦄, x ∈ S → y ∈ S →
        G.Adj x y → H.Adj (f x) (f y))
    (hfree : H.CliqueFreeOn T n) :
    G.CliqueFreeOn S n := by
  classical
  intro K hKS hK
  apply hfree (t := K.image f)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmap (hKS hx)
  refine ⟨isClique_image_of_mapsAdj K f hK.isClique
    (fun {_ _} hx hy hxy ↦
      hadj (hKS hx) (hKS hy) hxy), ?_⟩
  rw [Finset.card_image_of_injOn (hinj.mono hKS)]
  exact hK.card_eq

/-- A finite clique contained in a clique-free-on set has cardinality
strictly below the forbidden order. -/
theorem card_lt_of_cliqueFreeOn
    {G : SimpleGraph α} {S : Set α} {n : ℕ}
    (hfree : G.CliqueFreeOn S n)
    {K : Finset α}
    (hKS : (K : Set α) ⊆ S)
    (hK : G.IsClique K) :
    K.card < n := by
  classical
  by_contra hnot
  have hn : n ≤ K.card := Nat.le_of_not_gt hnot
  obtain ⟨L, hLK, hLcard⟩ :=
    Finset.exists_subset_card_eq (s := K) hn
  exact hfree ((Finset.coe_subset.mpr hLK).trans hKS)
    ⟨hK.subset hLK, hLcard⟩

/-- Cardinal form of the projection argument.  This is the common form
used when a replacement map is known to be injective only on the current
finite clique. -/
theorem card_lt_of_cliqueFreeOn_of_injOn
    {G : SimpleGraph α} {H : SimpleGraph β}
    {T : Set β} {n : ℕ}
    {K : Finset α} (f : α → β)
    (hinj : Set.InjOn f (K : Set α))
    (hmap : ∀ ⦃x⦄, x ∈ K → f x ∈ T)
    (hadj :
      ∀ ⦃x y⦄, x ∈ K → y ∈ K →
        G.Adj x y → H.Adj (f x) (f y))
    (hfree : H.CliqueFreeOn T n)
    (hK : G.IsClique K) :
    K.card < n := by
  classical
  let image : Finset β := K.image f
  have himage :
      H.IsClique image := by
    simpa [image] using isClique_image_of_mapsAdj K f hK hadj
  have hsubset : (image : Set β) ⊆ T := by
    intro y hy
    change y ∈ image at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmap hx
  have hlt : image.card < n :=
    card_lt_of_cliqueFreeOn hfree hsubset himage
  have hcard : image.card = K.card := by
    dsimp [image]
    exact Finset.card_image_of_injOn hinj
  rwa [hcard] at hlt

/-- Embedding-specialized cardinal bound. -/
theorem card_lt_of_cliqueFreeOn_of_embedding
    {W : Type*} [Fintype W]
    {H : SimpleGraph β} {T : Set β} {n : ℕ}
    (hfree : H.CliqueFreeOn T n)
    (f : W ↪ β)
    (hmap : ∀ x : W, f x ∈ T)
    (hclique :
      ∀ x y : W, x ≠ y → H.Adj (f x) (f y)) :
    Fintype.card W < n := by
  classical
  let K : Finset W := Finset.univ
  have hK : (⊤ : SimpleGraph W).IsClique K := by
    intro x _ y _ hxy
    simpa using hxy
  have hlt :=
    card_lt_of_cliqueFreeOn_of_injOn
      (G := (⊤ : SimpleGraph W)) (H := H)
      (K := K) (T := T) f
      (fun _ _ _ _ h ↦ f.injective h)
      (fun {_} _ ↦ hmap _)
      (fun {x y} _ _ hxy ↦
        hclique x y (by simpa using hxy))
      hfree hK
  simpa [K] using hlt

end SecondConnector
end RamseyIncrement
