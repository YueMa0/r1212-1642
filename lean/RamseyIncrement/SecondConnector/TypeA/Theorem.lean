/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Adjoin
import RamseyIncrement.SecondConnector.TypeA.BlueThroughW
import RamseyIncrement.SecondConnector.TypeA.OldEdges
import RamseyIncrement.SecondConnector.TypeA.RedThroughW

/-!
# The Type A second-connector extension

This module combines the old-edge and through-the-new-vertex arguments for
the Type A orientation.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeA

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- A Type A certificate yields the strengthened two-parameter extension. -/
theorem plus_caseA_extension
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (plusGraphA data) (k + 1) (s + 1) :=
  adjoin_isRamseyFree
    (extraAOldGraph_isRamseyFree data hG)
    (redNeighborhoodA_cliqueFree data hG)
    (blueNeighborhoodA_cliqueFree data hG)

end TypeA
end SecondConnector
end RamseyIncrement
