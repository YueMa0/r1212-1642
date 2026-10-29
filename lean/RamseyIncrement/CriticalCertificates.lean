/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Certificates
import RamseyIncrement.PlusCertificates
import RamseyIncrement.XSR

/-!
# Disjoint certificates in a critical coloring

This module formalizes Section 1's use of the XSR gap.  Every critical
`(k,s)` coloring with `5 ≤ k ≤ s` contains a red `K_(k-1)` and, outside
that chosen clique, a blue `K_(s-1)`.
-/

namespace RamseyIncrement

open SimpleGraph

variable {k s : ℕ}

/-- A critical coloring contains disjoint red and blue clique
certificates of the required orders. -/
theorem critical_has_disjoint_certificates
    (hk : 5 ≤ k) (hks : k ≤ s)
    (G : SimpleGraph (Fin (ramseyNumber k s - 1)))
    (hG : IsRamseyFree G k s) :
    Nonempty (Certificates G k s) := by
  classical
  have hs : 2 ≤ s := by omega
  have hredNot : ¬G.CliqueFree (k - 1) :=
    critical_has_red_certificate (by omega) hs G hG
  let c : Fin (k - 1) ↪ Fin (ramseyNumber k s - 1) :=
    cliqueCertificate hredNot
  have hc : G.IsClique (Set.range c) :=
    cliqueCertificate_isClique hredNot
  let W : Set (Fin (ramseyNumber k s - 1)) :=
    (Set.range c)ᶜ
  have hcCard : Fintype.card (Set.range c) = k - 1 := by
    simpa using Fintype.card_range c
  have hWcard :
      Fintype.card W =
        (ramseyNumber k s - 1) - (k - 1) := by
    rw [Fintype.card_compl_set, hcCard]
    simp
  have hxsr :=
    xsr_ramsey_increment (a := k) (b := s - 1) hk (by omega)
  have hspred : s - 1 + 1 = s := by omega
  rw [hspred] at hxsr
  have hWlarge :
      ramseyNumber k (s - 1) ≤ Fintype.card W := by
    omega
  let GW : SimpleGraph W := G.induce W
  have hGWred : GW.CliqueFree k := by
    exact (G.cliqueFree_induce_iff W k).2 hG.1.cliqueFreeOn
  have hblueNot : ¬GWᶜ.CliqueFree (s - 1) := by
    intro hblue
    exact ramseyNumber_forcesCard k (s - 1) W hWlarge GW
      ⟨hGWred, hblue⟩
  let iSubGraph :
      SimpleGraph.completeGraph (Fin (s - 1)) ↪g GWᶜ :=
    SimpleGraph.topEmbeddingOfNotCliqueFree hblueNot
  let i : Fin (s - 1) ↪ Fin (ramseyNumber k s - 1) :=
    iSubGraph.toEmbedding.trans (Function.Embedding.subtype _)
  have hi : Gᶜ.IsClique (Set.range i) := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hne rfl
    have hadj : GWᶜ.Adj (iSubGraph p) (iSubGraph q) :=
      iSubGraph.map_rel_iff.mpr (by simpa using hpq)
    simpa [GW, i, compl_induce] using hadj
  have hdisjoint : Disjoint (Set.range c) (Set.range i) := by
    rw [Set.disjoint_left]
    intro v hvC hvI
    obtain ⟨q, rfl⟩ := hvI
    have houtside : (iSubGraph q : Fin (ramseyNumber k s - 1)) ∈ W :=
      (iSubGraph q).property
    exact houtside hvC
  exact ⟨{
      c := c
      i := i
      c_isClique := hc
      i_isClique := hi
      disjoint := hdisjoint }⟩

/-- A critical coloring admits one of the four strengthened primal/dual
orientations required by the second-connector construction. -/
theorem critical_has_plus_orientation
    (hk : 5 ≤ k) (hks : k ≤ s)
    (G : SimpleGraph (Fin (ramseyNumber k s - 1)))
    (hG : IsRamseyFree G k s) :
    Nonempty (Certificates.PlusOrientation G k s) := by
  obtain ⟨cert⟩ :=
    critical_has_disjoint_certificates hk hks G hG
  exact cert.exists_plus_orientation hG hk hks

end RamseyIncrement
