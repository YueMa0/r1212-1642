/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Numerical
import RamseyIncrement.SecondConnector.TypeA.Theorem
import RamseyIncrement.SecondConnector.TypeB.Theorem

/-!
# The Ramsey increment theorem

This is the numerical conclusion of the complete constructive
formalization.
-/

namespace RamseyIncrement

/-- The two-connector construction.  Its final coloring has
`ramseyNumber k s + 2*k + 2*s - 1` vertices, so the Ramsey-number lower bound
has no final subtraction. -/
theorem ramsey_increment_plus
    {k s : ℕ} (hk : 5 ≤ k) (hks : k ≤ s) :
    ramseyNumber k s + 2 * k + 2 * s ≤
      ramseyNumber (k + 1) (s + 1) := by
  apply SecondConnector.ramsey_increment_plus_of_extensions hk hks
  · intro V G a b data hG
    exact SecondConnector.TypeA.plus_caseA_extension data hG
  · intro V G a b data hG
    exact SecondConnector.TypeB.plus_caseB_extension data hG

/-- Symmetric form, without choosing an order for the two
parameters. -/
theorem ramsey_increment_plus_symmetric
    {k s : ℕ} (hk : 5 ≤ k) (hs : 5 ≤ s) :
    ramseyNumber k s + 2 * k + 2 * s ≤
      ramseyNumber (k + 1) (s + 1) := by
  by_cases hks : k ≤ s
  · exact ramsey_increment_plus hk hks
  · have hsk : s ≤ k := by omega
    have h := ramsey_increment_plus hs hsk
    rw [ramseyNumber_symm s k,
      ramseyNumber_symm (s + 1) (k + 1)] at h
    omega

end RamseyIncrement
