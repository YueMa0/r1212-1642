/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Canonical
import RamseyIncrement.Switching.Clone
import RamseyIncrement.Switching.EdgeSafety

/-!
# The final switched graph

The graph is defined declaratively.  We first form the two canonical lifts,
add the red-joined clone, remove exactly the edges recolored blue, and add
exactly the edges recolored red.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- Nested tagged vertex type used by the actual construction. -/
abbrev Vertex (V : Type*) (k s : ℕ) :=
  CloneVertex (Canonical.Vertex V k s)

namespace Vertex

variable (cert : Certificates.OrderedCertificates G k s)

abbrev core (v : V) : Vertex V k s :=
  .inl (.core (.core v))

abbrev a (p : Fin (k - 1)) : Vertex V k s :=
  .inl (.core (.a p))

abbrev b (p : Fin (k - 1)) : Vertex V k s :=
  .inl (.core (.b p))

abbrev x (r : Option (Fin (s - 1))) : Vertex V k s :=
  .inl (.a ((Canonical.outerIndexEquiv
    (le_trans (by decide : 1 ≤ 5)
      cert.five_le_s)).symm r))

abbrev y (r : Option (Fin (s - 1))) : Vertex V k s :=
  .inl (.b ((Canonical.outerIndexEquiv
    (le_trans (by decide : 1 ≤ 5)
      cert.five_le_s)).symm r))

abbrev z : Vertex V k s :=
  CloneVertex.z

abbrev c0 : Fin (k - 1) :=
  Certificates.c0Index cert.five_le_k

abbrev i1 : Fin (s - 1) :=
  Certificates.i1Index' cert.five_le_s

abbrev c2 : Fin (k - 1) :=
  Certificates.c2Index cert.five_le_k

end Vertex

/-- The graph `F` before cloning. -/
noncomputable def canonicalGraph
    (cert : Certificates.OrderedCertificates G k s) :
    SimpleGraph (Canonical.Vertex V k s) :=
  Canonical.graph G cert.toCertificates cert.five_le_k
    (le_trans (by decide : 1 ≤ 5)
      cert.five_le_s)

/-- The graph after adjoining `z` as a red-joined clone of `b₀`, before
any switches. -/
noncomputable def preGraph
    (cert : Certificates.OrderedCertificates G k s) :
    SimpleGraph (Vertex V k s) :=
  redJoinedClone (canonicalGraph cert) (.core (.b (Vertex.c0 cert)))

/-- Oriented list of the edges switched from blue to red. -/
def addedRedRel (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → Vertex V k s → Prop :=
  fun u v ↦
    (∃ q ∈ cert.T,
      u = Vertex.a (Vertex.c0 cert) ∧ v = Vertex.y cert (some q)) ∨
    (u = Vertex.b (Vertex.c0 cert) ∧ v = Vertex.y cert none) ∨
    (u = Vertex.b (Vertex.c0 cert) ∧
      v = Vertex.b (Vertex.c2 cert))

/-- Oriented list of the edges switched from red to blue. -/
def removedRedRel (cert : Certificates.OrderedCertificates G k s) :
    Vertex V k s → Vertex V k s → Prop :=
  fun u v ↦
    (∃ q ∈ cert.T,
      u = Vertex.b (Vertex.c0 cert) ∧ v = Vertex.y cert (some q)) ∨
    (u = Vertex.b (Vertex.c0 cert) ∧
      v = Vertex.x cert (some (Vertex.i1 cert))) ∨
    (u = Vertex.b (Vertex.c0 cert) ∧ v = Vertex.x cert none) ∨
    (∃ q, q ≠ Vertex.i1 cert ∧
      u = Vertex.z ∧ v = Vertex.x cert (some q)) ∨
    (∃ q ∈ cert.E,
      u = Vertex.a (Vertex.c0 cert) ∧ v = Vertex.x cert (some q)) ∨
    (cert.E.Nonempty ∧
      u = Vertex.y cert (some (Vertex.i1 cert)) ∧ v = Vertex.y cert none) ∨
    (∃ q ∈ cert.E, 2 ≤ q.val ∧
      u = Vertex.y cert (some (Vertex.i1 cert)) ∧
        v = Vertex.y cert (some q))

/-- The (symmetric, loopless) graph consisting of newly red edges. -/
def addedRedGraph (cert : Certificates.OrderedCertificates G k s) :
    SimpleGraph (Vertex V k s) :=
  SimpleGraph.fromRel (addedRedRel cert)

/-- The (symmetric, loopless) graph consisting of edges recolored blue. -/
def removedRedGraph (cert : Certificates.OrderedCertificates G k s) :
    SimpleGraph (Vertex V k s) :=
  SimpleGraph.fromRel (removedRedRel cert)

/-- The final graph `H`. -/
noncomputable def finalGraph
    (cert : Certificates.OrderedCertificates G k s) :
    SimpleGraph (Vertex V k s) :=
  (preGraph cert \ removedRedGraph cert) ⊔ addedRedGraph cert

theorem final_adj_iff
    (cert : Certificates.OrderedCertificates G k s)
    (u v : Vertex V k s) :
    (finalGraph cert).Adj u v ↔
      (preGraph cert).Adj u v ∧ ¬(removedRedGraph cert).Adj u v ∨
        (addedRedGraph cert).Adj u v :=
  Iff.rfl

/-- Every red edge present only after switching belongs to the explicit
blue-to-red switch graph. -/
theorem classify_new_red_edge
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (hfinal : (finalGraph cert).Adj u v)
    (hpre : ¬(preGraph cert).Adj u v) :
    (addedRedGraph cert).Adj u v := by
  rcases (final_adj_iff cert u v).1 hfinal with h | h
  · exact False.elim (hpre h.1)
  · exact h

/-- Every blue edge present only after switching belongs to the explicit
red-to-blue switch graph. -/
theorem classify_new_blue_edge
    (cert : Certificates.OrderedCertificates G k s)
    {u v : Vertex V k s}
    (hfinal : (finalGraph cert)ᶜ.Adj u v)
    (hpre : ¬(preGraph cert)ᶜ.Adj u v) :
    (removedRedGraph cert).Adj u v := by
  have huv : u ≠ v := (SimpleGraph.compl_adj _ _ _).1 hfinal |>.1
  have hnfinal : ¬(finalGraph cert).Adj u v :=
    (SimpleGraph.compl_adj _ _ _).1 hfinal |>.2
  have hpreRed : (preGraph cert).Adj u v := by
    by_contra h
    exact hpre ((SimpleGraph.compl_adj _ _ _).2 ⟨huv, h⟩)
  by_contra hremoved
  exact hnfinal ((final_adj_iff cert u v).2
    (Or.inl ⟨hpreRed, hremoved⟩))

@[simp]
theorem card_vertex [Fintype V]
    (cert : Certificates.OrderedCertificates G k s) :
    Fintype.card (Vertex V k s) =
      Fintype.card V + 2 * k + 2 * s - 1 := by
  rw [card_cloneVertex, Canonical.card_vertex]
  have hk := cert.five_le_k
  omega

end Switching
end RamseyIncrement
