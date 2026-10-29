/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Canonical
import RamseyIncrement.RamseyNumber
import RamseyIncrement.Transport

/-!
# Constructive forms of the one-coordinate lift

This module packages the verified special lift as witnesses on the standard
finite vertex type `Fin n`.  No numerical Ramsey function is used here: the
results are constructive statements about a supplied coloring and clique
certificate.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s n : ℕ}

/-- The explicit special XSR lift, reindexed onto `Fin`, adds exactly
`2*k-2` vertices. -/
theorem specialLift_hasRamseyColoring
    (G : SimpleGraph (Fin n))
    (c : Fin (k - 1) ↪ Fin n)
    (hc : G.IsClique (Set.range c))
    (hk : 5 ≤ k)
    (hG : IsRamseyFree G k s) :
    HasRamseyColoring (n + 2 * k - 2) k (s + 1) := by
  let L := specialLift G c
  have hL : IsRamseyFree L k (s + 1) :=
    specialLift_isRamseyFree G c hc hk hG
  have hcard : Fintype.card (SpecialLiftVertex (Fin n) k) =
      n + 2 * k - 2 := by
    rw [SpecialLiftVertex.card]
    simp only [Fintype.card_fin]
    omega
  exact ⟨L.overFin hcard, hL.overFin hcard⟩

/-- The two canonical lifts, before the final clone-and-switch step, add
exactly `2*k+2*s-2` vertices. -/
theorem canonical_hasRamseyColoring
    (G : SimpleGraph (Fin n))
    (cert : Certificates G k s)
    (hk : 5 ≤ k) (hs5 : 5 ≤ s)
    (hG : IsRamseyFree G k s) :
    HasRamseyColoring (n + 2 * k + 2 * s - 2) (k + 1) (s + 1) := by
  have hs : 1 ≤ s :=
    le_trans (by decide : 1 ≤ 5) hs5
  let F := Canonical.graph G cert hk hs
  have hF : IsRamseyFree F (k + 1) (s + 1) :=
    Canonical.graph_isRamseyFree cert hk hs5 hG
  have hcard : Fintype.card (Canonical.Vertex (Fin n) k s) =
      n + 2 * k + 2 * s - 2 := by
    rw [Canonical.card_vertex]
    simp only [Fintype.card_fin]
    omega
  exact ⟨F.overFin hcard, hF.overFin hcard⟩

/-- A canonical embedding of a forbidden clique supplied by
`not CliqueFree`. -/
noncomputable def cliqueCertificate {n : ℕ}
    (h : ¬G.CliqueFree n) : Fin n ↪ V :=
  (SimpleGraph.topEmbeddingOfNotCliqueFree h).toEmbedding

theorem cliqueCertificate_isClique {n : ℕ}
    (h : ¬G.CliqueFree n) :
    G.IsClique (Set.range (cliqueCertificate h)) := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hne rfl
  exact (SimpleGraph.topEmbeddingOfNotCliqueFree h).map_rel_iff.mpr
    (by simpa using hpq)

/-- The Xu--Shao--Radziszowski one-coordinate Ramsey increment, derived
from the explicit special lift verified above. -/
theorem xsr_ramsey_increment {a b : ℕ}
    (ha : 5 ≤ a) (hb : 2 ≤ b) :
    ramseyNumber a b + 2 * a - 2 ≤ ramseyNumber a (b + 1) := by
  obtain ⟨G, hG⟩ :=
    exists_critical_coloring (k := a) (s := b) (by omega) (by omega)
  have hnot : ¬G.CliqueFree (a - 1) :=
    critical_has_red_certificate (by omega) hb G hG
  let c : Fin (a - 1) ↪ Fin (ramseyNumber a b - 1) :=
    cliqueCertificate hnot
  have hc : G.IsClique (Set.range c) :=
    cliqueCertificate_isClique hnot
  have hlift :=
    specialLift_hasRamseyColoring G c hc ha hG
  have hlower := ramseyNumber_lower_bound hlift
  have hpos := ramseyNumber_pos (by omega : 0 < a) (by omega : 0 < b)
  omega

/-- Complementary form of the XSR increment. -/
theorem xsr_ramsey_increment_left {a b : ℕ}
    (ha : 2 ≤ a) (hb : 5 ≤ b) :
    ramseyNumber a b + 2 * b - 2 ≤ ramseyNumber (a + 1) b := by
  rw [ramseyNumber_symm a b, ramseyNumber_symm (a + 1) b]
  exact xsr_ramsey_increment hb ha

end RamseyIncrement
