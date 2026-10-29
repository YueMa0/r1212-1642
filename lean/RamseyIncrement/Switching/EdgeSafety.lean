/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Basic

/-!
# Generic edge-switching safety lemmas

These lemmas isolate the common argument behind rows (R1)--(R4) and
(B1)--(B6): a forbidden clique newly created by an edge modification
contains a newly introduced edge, and deleting its two endpoints leaves a
clique in their common same-color neighborhood.
-/

namespace RamseyIncrement
namespace Switching

open Finset
open SimpleGraph

variable {V : Type*} [DecidableEq V]
variable {G G₀ G₁ : SimpleGraph V}
variable {u v : V} {n : ℕ} {t : Finset V}

/-- Removing two distinct specified vertices from an `(n+2)`-clique leaves
an `n`-clique contained in their common neighborhood. -/
theorem erasePair_to_commonNeighbors
    (ht : G.IsNClique (n + 2) t) (hu : u ∈ t) (hv : v ∈ t)
    (huv : u ≠ v) :
    G.IsNClique n ((t.erase u).erase v) ∧
      (↑((t.erase u).erase v) : Set V) ⊆ G.commonNeighbors u v := by
  have hv' : v ∈ t.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  constructor
  · constructor
    · exact ht.isClique.subset (by
        intro w hw
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2)
    · rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu,
        ht.card_eq]
      omega
  · intro w hw
    have hw' : w ∈ (t.erase u).erase v := hw
    obtain ⟨hwv, hwtu⟩ := Finset.mem_erase.mp hw'
    obtain ⟨hwu, hwt⟩ := Finset.mem_erase.mp hwtu
    exact G.mem_commonNeighbors.mpr
      ⟨ht.isClique hu hwt hwu.symm, ht.isClique hv hwt hwv.symm⟩

/-- A common-neighborhood bound rules out an `(n+2)`-clique containing
both endpoints. -/
theorem not_isNClique_of_mem_pair
    (hcommon : G.CliqueFreeOn (G.commonNeighbors u v) n)
    (ht : G.IsNClique (n + 2) t) (hu : u ∈ t) (hv : v ∈ t)
    (huv : u ≠ v) : False := by
  obtain ⟨hclique, hsubset⟩ :=
    erasePair_to_commonNeighbors ht hu hv huv
  exact hcommon hsubset hclique

omit [DecidableEq V] in
/-- If an old graph is `n`-clique-free but a new graph has an `n`-clique,
that clique contains an edge which is present only in the new graph. -/
theorem exists_new_edge_in_clique
    (h₀ : G₀.CliqueFree n) (ht : G₁.IsNClique n t) :
    ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧ G₁.Adj u v ∧ ¬G₀.Adj u v := by
  have hnot : ¬G₀.IsClique (t : Set V) := by
    intro hclique
    exact h₀ t ⟨hclique, ht.card_eq⟩
  rw [G₀.not_isClique_iff] at hnot
  obtain ⟨u, v, huv, hnonedge⟩ := hnot
  refine ⟨u, u.property, v, v.property, Subtype.coe_ne_coe.mpr huv, ?_, hnonedge⟩
  exact ht.isClique u.property v.property (Subtype.coe_ne_coe.mpr huv)

/-- Generic dangerous-edge reduction.

To prove that `G₁` remains `(n+2)`-clique-free after editing a
`(n+2)`-clique-free graph `G₀`, it suffices to classify every newly added
edge by `Dangerous` and prove that the common neighborhood of every
classified edge is `n`-clique-free in `G₁`.
-/
theorem cliqueFree_of_new_edges
    (Dangerous : V → V → Prop)
    (h₀ : G₀.CliqueFree (n + 2))
    (hclassify :
      ∀ ⦃u v⦄, G₁.Adj u v → ¬G₀.Adj u v → Dangerous u v)
    (hsafe :
      ∀ ⦃u v⦄, Dangerous u v →
        G₁.CliqueFreeOn (G₁.commonNeighbors u v) n) :
    G₁.CliqueFree (n + 2) := by
  intro t ht
  obtain ⟨u, hu, v, hv, huv, hnew, hold⟩ :=
    exists_new_edge_in_clique h₀ ht
  exact not_isNClique_of_mem_pair (hsafe (hclassify hnew hold))
    ht hu hv huv

end Switching
end RamseyIncrement
