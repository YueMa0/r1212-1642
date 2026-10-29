/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.CriticalCertificates
import RamseyIncrement.PlusCertificates
import RamseyIncrement.RamseyNumber
import RamseyIncrement.SecondConnector.Transport
import RamseyIncrement.SecondConnector.TypeA.Construction
import RamseyIncrement.SecondConnector.TypeB.Construction

/-!
# Numerical wrapper for the strengthened construction

This file separates the Ramsey-number arithmetic and the primal/dual
orientation dispatch from the branch-local clique proofs.  Once the Type A
and Type B extension theorems are supplied, the strengthened numerical bound
follows from a critical coloring.
-/

namespace RamseyIncrement
namespace SecondConnector

/-- The numerical consequence of verified Type A and Type B second-connector
extensions.  The hypotheses quantify uniformly over the vertex type so the
same two branch theorems apply in both the primal and dual orientations. -/
theorem ramsey_increment_plus_of_extensions
    {k s : ℕ} (hk : 5 ≤ k) (hks : k ≤ s)
    (hA :
      ∀ {V : Type} {G : SimpleGraph V} {a b : ℕ}
        (data : Certificates.PlusCaseAData G a b),
        IsRamseyFree G a b →
          IsRamseyFree (TypeA.plusGraphA data) (a + 1) (b + 1))
    (hB :
      ∀ {V : Type} {G : SimpleGraph V} {a b : ℕ}
        (data : Certificates.PlusCaseBData G a b),
        IsRamseyFree G a b →
          IsRamseyFree (TypeB.plusGraphB data) (a + 1) (b + 1)) :
    ramseyNumber k s + 2 * k + 2 * s ≤
      ramseyNumber (k + 1) (s + 1) := by
  obtain ⟨G, hG⟩ :=
    exists_critical_coloring (k := k) (s := s) (by omega) (by omega)
  obtain ⟨orientation⟩ := critical_has_plus_orientation hk hks G hG
  have hcoloring :
      HasRamseyColoring
        ((ramseyNumber k s - 1) + 2 * k + 2 * s)
        (k + 1) (s + 1) := by
    cases orientation with
    | primalA data =>
        exact plusGraph_hasRamseyColoring data.cert
          (TypeA.plusGraphA data) (hA data hG)
    | primalB data =>
        exact plusGraph_hasRamseyColoring data.cert
          (TypeB.plusGraphB data) (hB data hG)
    | dualA data =>
        exact plusGraph_hasRamseyColoring_dual data.cert
          (TypeA.plusGraphA data) (hA data hG.symm)
    | dualB data =>
        exact plusGraph_hasRamseyColoring_dual data.cert
          (TypeB.plusGraphB data) (hB data hG.symm)
  have hlower := ramseyNumber_lower_bound hcoloring
  have hpos : 0 < ramseyNumber k s :=
    ramseyNumber_pos (by omega) (by omega)
  omega

end SecondConnector
end RamseyIncrement
