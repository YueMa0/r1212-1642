/-
Rule R*: tools for Parts II and III (cliques through `u`).
-/
import RamseyIncrement.ThirdConnector.RedEdges

/-!
# Projection and slot counting

Parts II and III bound cliques in the two color neighborhoods of `u` in two
ways:

* projection: map the clique to vertices of `G` so that distinct members go to
  adjacent vertices; the bound then comes from `G` being `(k,s)`-free;
* slots: inject the clique into `Fin m`.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-- A clique whose members map to pairwise adjacent vertices of `G'` cannot
have `n` members when `G'` has no `n`-clique. -/
theorem false_of_projection {W : Type*} {H : SimpleGraph W} {G' : SimpleGraph V} {n : ℕ}
    (hfree : G'.CliqueFree n) {t : Finset W} (ht : H.IsNClique n t) (f : W → V)
    (hf : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G'.Adj (f u) (f v)) : False := by
  classical
  have hinj : Set.InjOn f t := by
    intro u hu v hv huv
    by_contra hne
    exact (hf u hu v hv hne).ne huv
  apply hfree (t.image f)
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.coe_image] at ha hb
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    exact hf u hu v hv (fun h ↦ hab (h ▸ rfl))
  · rw [Finset.card_image_of_injOn hinj, ht.card_eq]

/-- A finite set that injects into `Fin m` has at most `m` members. -/
theorem card_le_of_slot {W : Type*} {t : Finset W} {m : ℕ} (f : W → Fin m)
    (hinj : Set.InjOn f t) : t.card ≤ m := by
  have := Finset.card_le_card_of_injOn f (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  simpa using this

section

variable (data : Certificates.PlusCaseAData G k s)

/-- The blue neighborhood of `u`: `I ∖ i₀` and the core vertices blue to `i₀`,
the odd `a`, `b₂`, `x_q` (`q ≠ 0`), all `y_q`, `z` and `w`. -/
theorem mem_blueU {u : SecondConnector.Vertex V k s} (hu : ¬redToU data u) :
    (∃ v, (∀ p, v ≠ data.cert.c p) ∧ v ≠ data.cert.i (i0Index data) ∧
        ¬G.Adj (data.cert.i (i0Index data)) v ∧ u = core v) ∨
      (∃ p : Fin (k - 1), p.val % 2 = 1 ∧ u = a p) ∨ u = b (c2Index data) ∨
      (∃ q, q ≠ i0Index data ∧ u = x data.cert (some q)) ∨
      (∃ q, u = y data.cert (some q)) ∨ u = z ∨ u = w := by
  rcases vertex_cases data u with ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl | rfl
  · left
    simp only [redToU_core, not_or, not_exists] at hu
    exact ⟨v, fun p h ↦ hu.1 p h, hu.2.1, hu.2.2, rfl⟩
  · right; left
    simp only [redToU_a] at hu
    exact ⟨p, by omega, rfl⟩
  · right; right; left
    simp only [redToU_b, ne_eq, not_not] at hu
    rw [hu]
  · right; right; right; left
    cases r with
    | none => simp at hu
    | some q =>
        simp at hu
        exact ⟨q, hu, rfl⟩
  · right; right; right; right; left
    cases r with
    | none => simp at hu
    | some q => exact ⟨q, rfl⟩
  · right; right; right; right; right; left; rfl
  · right; right; right; right; right; right; rfl

/-- The red neighborhood of `u`: `C`, `i₀` and the core vertices red to `i₀`,
the even `a`, the `b_p` with `p ≠ 2`, `x₀`, `x_*` and `y_*`. -/
theorem mem_redU {u : SecondConnector.Vertex V k s} (hu : redToU data u) :
    (∃ v, ((∃ p, v = data.cert.c p) ∨ v = data.cert.i (i0Index data) ∨
        G.Adj (data.cert.i (i0Index data)) v) ∧ u = core v) ∨
      (∃ p : Fin (k - 1), p.val % 2 = 0 ∧ u = a p) ∨
      (∃ p, p ≠ c2Index data ∧ u = b p) ∨
      u = x data.cert none ∨ u = x data.cert (some (i0Index data)) ∨
      u = y data.cert none := by
  rcases vertex_cases data u with ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨v, hu, rfl⟩
  · exact Or.inr (Or.inl ⟨p, hu, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, hu, rfl⟩))
  · simp at hu
    rcases hu with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · simp at hu
    subst hu
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact absurd hu (redToU_z data)
  · exact absurd hu (redToU_w data)

end

end ThirdConnector
end RamseyIncrement
