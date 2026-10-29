/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Dispatch
import RamseyIncrement.Switching.RedCases

/-!
# The completed red side of the switching table

All four red rows are now discharged.  This theorem leaves only the six
blue row families as explicit hypotheses.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

theorem final_isRamseyFree_of_blue_rows
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hB1 :
      ∀ q ∈ cert.T,
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)))
          (s - 1))
    (hB2 :
      (finalGraph cert)ᶜ.CliqueFreeOn
        ((finalGraph cert)ᶜ.commonNeighbors
          (Vertex.b (Vertex.c0 cert))
          (Vertex.x cert (some (Vertex.i1 cert)))) (s - 1))
    (hB3 :
      (finalGraph cert)ᶜ.CliqueFreeOn
        ((finalGraph cert)ᶜ.commonNeighbors
          (Vertex.b (Vertex.c0 cert)) (Vertex.x cert none)) (s - 1))
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
  exact final_isRamseyFree_of_explicit_rows cert hG
    (red_safe_b0_z cert hG)
    (fun _ hq ↦ red_safe_a0_y cert hG hq)
    (red_safe_b0_ystar cert)
    (red_safe_b0_b2 cert hG)
    hB1 hB2 hB3 hB4 hB5 hB6star hB6large

end Switching
end RamseyIncrement
