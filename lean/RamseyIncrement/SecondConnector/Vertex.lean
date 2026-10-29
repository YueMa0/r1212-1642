/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Adjoin
import RamseyIncrement.Switching.Construction

/-!
# Vertices after adjoining the second connector

The old vertices are the actual vertices of `Switching.finalGraph`; the
single new summand is the second connector `w`.
-/

namespace RamseyIncrement
namespace SecondConnector

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- The switched vertices together with the second connector. -/
abbrev Vertex (V : Type*) (k s : ℕ) :=
  AdjoinVertex (Switching.Vertex V k s)

namespace Vertex

/-- Inclusion of a vertex of the first-connector graph. -/
abbrev old (v : Switching.Vertex V k s) : Vertex V k s :=
  AdjoinVertex.old v

/-- The second connector. -/
abbrev w : Vertex V k s :=
  AdjoinVertex.w

end Vertex

/-- Adding the second connector raises the switched-vertex count by one. -/
@[simp]
theorem card_plusVertex [Fintype V]
    (cert : Certificates.OrderedCertificates G k s) :
    Fintype.card (Vertex V k s) =
      Fintype.card V + 2 * k + 2 * s := by
  rw [card_adjoinVertex, Switching.card_vertex cert]
  have hk := cert.five_le_k
  omega

end SecondConnector
end RamseyIncrement
