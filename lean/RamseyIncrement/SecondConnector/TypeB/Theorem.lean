/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Adjoin
import RamseyIncrement.SecondConnector.TypeB.BlueThroughW
import RamseyIncrement.SecondConnector.TypeB.OldEdges
import RamseyIncrement.SecondConnector.TypeB.RedThroughW

/-!
# The Type B second-connector extension

This module combines the old-edge and through-the-new-vertex arguments for
the Type B orientation.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- A Type B certificate yields the strengthened two-parameter extension. -/
theorem plus_caseB_extension
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (plusGraphB data) (k + 1) (s + 1) :=
  adjoin_isRamseyFree
    (extraBOldGraph_isRamseyFree data hG)
    (redNeighborhoodB_cliqueFree data hG)
    (blueNeighborhoodB_cliqueFree data hG)

end TypeB
end SecondConnector
end RamseyIncrement
