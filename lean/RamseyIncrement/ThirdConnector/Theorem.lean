/-
Rule R*: the main theorem, assembled from the three parts of the proof.
-/
import RamseyIncrement.ThirdConnector.RedU
import RamseyIncrement.Switching.EdgeSafety
import RamseyIncrement.Transport

/-!
# The rule R* (theorem)

Section 4 of `02_expert_report.md`:

* Part I: a monochromatic clique of the switched graph that uses a switched
  edge lies, apart from the edge, in the common neighborhood of its two
  endpoints; those neighborhoods are small.  Every other clique is a clique
  of `H⁺`, which is `(k+1, s+1)`-free by Tatarevic's Type A theorem.
* Part II: the red neighborhood of `u` has no red `K_k`.
* Part III: the blue neighborhood of `u` has no blue `K_s`.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-! ## Part I: the switched edges -/

/-- A red edge of the switched graph that is not red in `H⁺` is an added edge. -/
theorem classify_new_red (data : Certificates.PlusCaseAData G k s)
    {u v : SecondConnector.Vertex V k s}
    (h₁ : (oldGraph data).Adj u v)
    (h₀ : ¬(SecondConnector.TypeA.plusGraphA data).Adj u v) :
    (addedRedGraph data).Adj u v := by
  rcases (oldGraph_adj_iff data u v).1 h₁ with h | h
  · exact absurd h.1 h₀
  · exact h

/-- A blue edge of the switched graph that is not blue in `H⁺` is a removed
edge. -/
theorem classify_new_blue (data : Certificates.PlusCaseAData G k s)
    {u v : SecondConnector.Vertex V k s}
    (h₁ : (oldGraph data)ᶜ.Adj u v)
    (h₀ : ¬(SecondConnector.TypeA.plusGraphA data)ᶜ.Adj u v) :
    (removedRedGraph data).Adj u v := by
  rw [SimpleGraph.compl_adj] at h₁ h₀
  have hred : (SecondConnector.TypeA.plusGraphA data).Adj u v := by
    by_contra h
    exact h₀ ⟨h₁.1, h⟩
  by_contra hrem
  exact h₁.2 ((oldGraph_adj_iff data u v).2 (Or.inl ⟨hred, hrem⟩))

/-- Part I(3): the common red neighborhood of an added edge `a_p y₀`
(`p` odd) has no red `K_(k-1)`.  Neither (P1) nor (P2) is needed. -/
theorem red_common_cliqueFree (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {u v : SecondConnector.Vertex V k s} (h : (addedRedGraph data).Adj u v) :
    (oldGraph data).CliqueFreeOn ((oldGraph data).commonNeighbors u v) (k - 1) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [addedRedGraph_adj_iff] at h
  obtain ⟨p, hp, h⟩ := h
  simp only [Switching.SymmPair] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact red_common_ap_y0_cliqueFree data hE hp
  · rw [SimpleGraph.commonNeighbors_symm]
    exact red_common_ap_y0_cliqueFree data hE hp

/-- Part I(1), (2): the common blue neighborhoods of the removed edges `c₂x₀`
and `i₀x_*` have no blue `K_(s-1)`. -/
theorem blue_common_cliqueFree (data : Certificates.PlusCaseAData G k s)
    (hP1 : P1 data) (hP2 : P2 data) (hG : IsRamseyFree G k s)
    {u v : SecondConnector.Vertex V k s} (h : (removedRedGraph data).Adj u v) :
    (oldGraph data)ᶜ.CliqueFreeOn ((oldGraph data)ᶜ.commonNeighbors u v) (s - 1) := by
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  rw [removedRedGraph_adj_iff] at h
  simp only [removedRedRel, Switching.SymmPair] at h
  rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact blue_common_c2_x0_cliqueFree data hE hP2
  · rw [SimpleGraph.commonNeighbors_symm]
    exact blue_common_c2_x0_cliqueFree data hE hP2
  · exact blue_common_i0_xStar_cliqueFree data hE hP1 hP2
  · rw [SimpleGraph.commonNeighbors_symm]
    exact blue_common_i0_xStar_cliqueFree data hE hP1 hP2

/-- Part I: the switched graph is still `(k+1, s+1)`-free. -/
theorem oldGraph_isRamseyFree (data : Certificates.PlusCaseAData G k s)
    (hP1 : P1 data) (hP2 : P2 data) (hG : IsRamseyFree G k s) :
    IsRamseyFree (oldGraph data) (k + 1) (s + 1) := by
  classical
  have hH := SecondConnector.TypeA.plus_caseA_extension data hG
  have hk := data.cert.five_le_k
  have hs := data.cert.five_le_s
  have ek : k + 1 = (k - 1) + 2 := by omega
  have es : s + 1 = (s - 1) + 2 := by omega
  constructor
  · rw [ek]
    exact Switching.cliqueFree_of_new_edges (addedRedGraph data).Adj
      (G₀ := SecondConnector.TypeA.plusGraphA data) (by rw [← ek]; exact hH.1)
      (fun _ _ h₁ h₀ ↦ classify_new_red data h₁ h₀)
      (fun _ _ h ↦ red_common_cliqueFree data hG h)
  · rw [es]
    exact Switching.cliqueFree_of_new_edges (removedRedGraph data).Adj
      (G₀ := (SecondConnector.TypeA.plusGraphA data)ᶜ) (by rw [← es]; exact hH.2)
      (fun _ _ h₁ h₀ ↦ classify_new_blue data h₁ h₀)
      (fun _ _ h ↦ blue_common_cliqueFree data hP1 hP2 hG h)

/-! ## Parts II and III: cliques through `u` -/

/-- Part II: the red neighborhood of `u` has no red `K_k`.  Uses (P1). -/
theorem redNeighborhood_cliqueFree (data : Certificates.PlusCaseAData G k s)
    (hP1 : P1 data) (hG : IsRamseyFree G k s) :
    (oldGraph data).CliqueFreeOn {v | redToU data v} k :=
  redU_cliqueFree data hP1 hG

/-- Part III: the blue neighborhood of `u` has no blue `K_s`.  Neither (P1)
nor (P2) is needed. -/
theorem blueNeighborhood_cliqueFree (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (oldGraph data)ᶜ.CliqueFreeOn {v | ¬redToU data v} s :=
  blueU_cliqueFree data hG

/-! ## The theorem -/

/-- **Rule R\***.  For Type A certificates with (P1) and (P2), the coloring
`O` is `(k+1, s+1)`-free. -/
theorem rstar_isRamseyFree (data : Certificates.PlusCaseAData G k s)
    (hP1 : P1 data) (hP2 : P2 data) (hG : IsRamseyFree G k s) :
    IsRamseyFree (rstarGraph data) (k + 1) (s + 1) :=
  SecondConnector.adjoin_isRamseyFree
    (oldGraph_isRamseyFree data hP1 hP2 hG)
    (redNeighborhood_cliqueFree data hP1 hG)
    (blueNeighborhood_cliqueFree data hG)

/-- Numerical form: a `(k,s)`-coloring on `n` vertices with such certificates
gives a `(k+1, s+1)`-coloring on `n + 2k + 2s + 1` vertices. -/
theorem rstar_hasRamseyColoring {n : ℕ} {G : SimpleGraph (Fin n)}
    (data : Certificates.PlusCaseAData G k s)
    (hP1 : P1 data) (hP2 : P2 data) (hG : IsRamseyFree G k s) :
    HasRamseyColoring (n + 2 * k + 2 * s + 1) (k + 1) (s + 1) := by
  have hcard : Fintype.card (Vertex (Fin n) k s) = n + 2 * k + 2 * s + 1 := by
    simpa using card_vertex data
  exact ⟨(rstarGraph data).overFin hcard,
    (rstar_isRamseyFree data hP1 hP2 hG).overFin hcard⟩

end ThirdConnector
end RamseyIncrement
