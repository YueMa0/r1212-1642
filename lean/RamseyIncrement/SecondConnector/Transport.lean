/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Vertex
import RamseyIncrement.Transport

/-!
# Transporting a two-connector coloring

The branch constructions use the tagged second-connector vertex type.  This
module transports any verified branch graph to the canonical finite type used
by the numerical Ramsey-number argument.  The symmetric form is convenient
when the strengthened orientation lemma selects the complementary coloring.
-/

namespace RamseyIncrement
namespace SecondConnector

variable {n k s : ℕ} {G : SimpleGraph (Fin n)}

/-- Transport a verified two-connector graph to `Fin (n + 2*k + 2*s)`. -/
theorem plusGraph_hasRamseyColoring
    (cert : Certificates.OrderedCertificates G k s)
    (H : SimpleGraph (Vertex (Fin n) k s))
    (hH : IsRamseyFree H (k + 1) (s + 1)) :
    HasRamseyColoring (n + 2 * k + 2 * s) (k + 1) (s + 1) := by
  have hcard :
      Fintype.card (Vertex (Fin n) k s) = n + 2 * k + 2 * s := by
    simpa using card_plusVertex cert
  exact ⟨H.overFin hcard, hH.overFin hcard⟩

/-- Complement and transport a verified graph built in the dual
orientation. -/
theorem plusGraph_hasRamseyColoring_dual
    (cert : Certificates.OrderedCertificates Gᶜ s k)
    (H : SimpleGraph (Vertex (Fin n) s k))
    (hH : IsRamseyFree H (s + 1) (k + 1)) :
    HasRamseyColoring (n + 2 * k + 2 * s) (k + 1) (s + 1) := by
  have hcard :
      Fintype.card (Vertex (Fin n) s k) = n + 2 * k + 2 * s := by
    have h := card_plusVertex cert
    have h' :
        Fintype.card (Vertex (Fin n) s k) = n + 2 * s + 2 * k := by
      simpa only [Fintype.card_fin] using h
    omega
  exact ⟨Hᶜ.overFin hcard, hH.symm.overFin hcard⟩

end SecondConnector
end RamseyIncrement
