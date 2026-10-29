/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.BlueCoreAssembly
import RamseyIncrement.Switching.BlueCasesB4B5

/-!
# Assembly after blue rows B4 and B5

Rows (B1)--(B5) are discharged.  Only the two endpoint forms of row (B6)
remain as hypotheses.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

theorem final_isRamseyFree_of_b6_rows
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB6star :
      cert.E.Nonempty →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.y cert (some (Vertex.i1 cert)))
            (Vertex.y cert none)) (s - 1))
    (hB6large :
      ∀ q ∈ cert.E, 2 ≤ q.val →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.y cert (some (Vertex.i1 cert)))
            (Vertex.y cert (some q))) (s - 1)) :
    IsRamseyFree (finalGraph cert) (k + 1) (s + 1) := by
  exact final_isRamseyFree_of_remaining_blue_rows cert hG
    (fun _ hq ↦ blue_case_b4 cert hG hq)
    (fun _ hq ↦ blue_case_b5 cert hG hq)
    hB6star hB6large

end Switching
end RamseyIncrement
