/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.BlueAssembly
import RamseyIncrement.Switching.BlueCasesB6

/-!
# The switching extension theorem

This module combines all four red and six blue switching rows.  It is the
formal version of the switching lemma in Section 4 of `PROOF.md`.
-/

namespace RamseyIncrement
namespace Switching

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- An ordered `(k,s)` certificate produces a `(k+1,s+1)`-free coloring
on the final switched graph. -/
theorem switching_extension
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (finalGraph cert) (k + 1) (s + 1) := by
  have hB1 : B1RowSafety cert :=
    fun q hq ↦ blue_case_b1 cert hG hq
  exact final_isRamseyFree_of_b6_rows cert hG
    (blue_case_b6_star_of_b1 cert hG hB1)
    (fun _ hq hq2 ↦
      blue_case_b6_large_of_b1 cert hG hB1 hq hq2)

end Switching
end RamseyIncrement
