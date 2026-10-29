/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.ChangedEdges

/-!
# Assembling the switching rows

The mathematical content of the switching table is expressed as local
common-neighborhood safety.  These generic lemmas turn those row facts into
global red and blue clique-freeness of the final graph.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- The red rows imply global red clique-freeness.  The special `b₀z`
row handles a forbidden clique already present in the red-joined clone;
all other cases contain an explicitly added red edge. -/
theorem final_red_cliqueFree_of_row_safety
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hb0z :
      (finalGraph cert).CliqueFreeOn
        ((finalGraph cert).commonNeighbors
          (Vertex.b (Vertex.c0 cert)) Vertex.z)
        (k - 1))
    (hadded :
      ∀ ⦃u v : Vertex V k s⦄,
        (addedRedGraph cert).Adj u v →
        (finalGraph cert).CliqueFreeOn
          ((finalGraph cert).commonNeighbors u v) (k - 1)) :
    (finalGraph cert).CliqueFree (k + 1) := by
  classical
  intro t ht
  have ht' : (finalGraph cert).IsNClique ((k - 1) + 2) t := by
    convert ht using 1
    have hk := cert.five_le_k
    omega
  by_cases hpre : (preGraph cert).IsClique (t : Set (Vertex V k s))
  · have hpreClique : (preGraph cert).IsNClique (k + 1) t :=
      ⟨hpre, ht.card_eq⟩
    obtain ⟨hb0, hz⟩ :=
      preGraph_red_clique_contains_b0_z cert hG hpreClique
    exact not_isNClique_of_mem_pair hb0z ht' hb0 hz (by simp)
  · rw [(preGraph cert).not_isClique_iff] at hpre
    obtain ⟨u, v, huv, hnotPre⟩ := hpre
    have hfinal :
        (finalGraph cert).Adj u.1 v.1 :=
      ht.isClique u.2 v.2 (Subtype.coe_ne_coe.mpr huv)
    have hadd :
        (addedRedGraph cert).Adj u.1 v.1 :=
      classify_new_red_edge cert hfinal hnotPre
    exact not_isNClique_of_mem_pair (hadded hadd) ht'
      u.2 v.2 (Subtype.coe_ne_coe.mpr huv)

/-- The blue rows imply global blue clique-freeness, since the graph before
switching was already blue-clique-free and every new blue edge belongs to
the explicit removed-red graph. -/
theorem final_blue_cliqueFree_of_row_safety
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hremoved :
      ∀ ⦃u v : Vertex V k s⦄,
        (removedRedGraph cert).Adj u v →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors u v) (s - 1)) :
    (finalGraph cert)ᶜ.CliqueFree (s + 1) := by
  classical
  intro t ht
  have ht' : (finalGraph cert)ᶜ.IsNClique ((s - 1) + 2) t := by
    convert ht using 1
    have hs := cert.two_le_s
    omega
  obtain ⟨u, hu, v, hv, huv, hfinal, hnotPre⟩ :=
    exists_new_edge_in_clique
      (preGraph_compl_cliqueFree cert hG) ht
  have hremovedEdge :
      (removedRedGraph cert).Adj u v :=
    classify_new_blue_edge cert hfinal hnotPre
  exact not_isNClique_of_mem_pair (hremoved hremovedEdge)
    ht' hu hv huv

/-- Combined assembly theorem for callers which have already discharged all
red and blue rows. -/
theorem final_isRamseyFree_of_row_safety
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hb0z :
      (finalGraph cert).CliqueFreeOn
        ((finalGraph cert).commonNeighbors
          (Vertex.b (Vertex.c0 cert)) Vertex.z)
        (k - 1))
    (hadded :
      ∀ ⦃u v : Vertex V k s⦄,
        (addedRedGraph cert).Adj u v →
        (finalGraph cert).CliqueFreeOn
          ((finalGraph cert).commonNeighbors u v) (k - 1))
    (hremoved :
      ∀ ⦃u v : Vertex V k s⦄,
        (removedRedGraph cert).Adj u v →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors u v) (s - 1)) :
    IsRamseyFree (finalGraph cert) (k + 1) (s + 1) := by
  classical
  exact
    ⟨final_red_cliqueFree_of_row_safety cert hG hb0z hadded,
      final_blue_cliqueFree_of_row_safety cert hG hremoved⟩

end Switching
end RamseyIncrement
