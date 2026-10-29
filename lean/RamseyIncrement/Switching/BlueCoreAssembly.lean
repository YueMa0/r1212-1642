/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.RedAssembly
import RamseyIncrement.Switching.BlueCases

/-!
# Assembly after the first three blue rows

Rows (B1)--(B3) are discharged by `BlueCases`.  This theorem leaves only
rows (B4), (B5), and the two families in (B6) as explicit hypotheses.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

theorem final_isRamseyFree_of_remaining_blue_rows
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB4 :
      ∀ q, q ≠ Vertex.i1 cert →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            Vertex.z (Vertex.x cert (some q))) (s - 1))
    (hB5 :
      ∀ q ∈ cert.E,
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.a (Vertex.c0 cert)) (Vertex.x cert (some q)))
          (s - 1))
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
  exact final_isRamseyFree_of_blue_rows cert hG
    (fun q hq ↦ blue_case_b1 cert hG hq)
    (blue_case_b2 cert hG)
    (blue_case_b3 cert hG)
    hB4 hB5 hB6star hB6large

end Switching
end RamseyIncrement
