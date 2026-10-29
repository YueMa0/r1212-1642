/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Certificates
import RamseyIncrement.SpecialLift
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The two canonical special lifts

This file composes the first special lift with its complementary counterpart.
The resulting nested tagged type has exactly the `G`, `A`, `B`, `X`, and `Y`
blocks of Section 2.
-/

namespace RamseyIncrement

open SimpleGraph

namespace Canonical

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- Identify `Fin s` with the ordinary indices `Fin (s-1)` plus `*`, with
`Fin.last` corresponding to `*`. -/
def outerIndexEquiv (hs : 1 ≤ s) : Fin s ≃ Option (Fin (s - 1)) :=
  (finCongr (Nat.sub_add_cancel hs).symm).trans
    finSuccEquivLast

/-- The blue certificate `J = I ∪ {a₀}` in the first lift, expressed on
the `Option` index type in which `none` denotes `*`. -/
def secondCertificateAt (cert : Certificates G k s) (hk : 5 ≤ k) :
    Option (Fin (s - 1)) → SpecialLiftVertex V k
  | some q => .core (cert.i q)
  | none => .a (Certificates.c0Index hk)

theorem secondCertificateAt_injective
    (cert : Certificates G k s) (hk : 5 ≤ k) :
    Function.Injective (secondCertificateAt cert hk) := by
  intro r t h
  cases r with
  | none =>
      cases t with
      | none => rfl
      | some _ => simp [secondCertificateAt] at h
  | some r =>
      cases t with
      | none => simp [secondCertificateAt] at h
      | some t =>
          apply congrArg some
          exact cert.i.injective (SpecialLiftVertex.core.inj h)

/-- The `Fin s`-indexed embedding used by the complementary second lift. -/
def secondCertificate (cert : Certificates G k s) (hk : 5 ≤ k)
    (hs : 1 ≤ s) : Fin s ↪ SpecialLiftVertex V k :=
  (outerIndexEquiv hs).toEmbedding.trans
    ⟨secondCertificateAt cert hk, secondCertificateAt_injective cert hk⟩

@[simp]
theorem secondCertificate_apply (cert : Certificates G k s) (hk : 5 ≤ k)
    (hs : 1 ≤ s) (r : Fin s) :
    secondCertificate cert hk hs r =
      secondCertificateAt cert hk (outerIndexEquiv hs r) :=
  rfl

/-- `I ∪ {a₀}` is a blue clique in the first lift. -/
theorem secondCertificate_isClique
    (cert : Certificates G k s) (hk : 5 ≤ k) (hs : 1 ≤ s) :
    (specialLift G cert.c)ᶜ.IsClique
      (Set.range (secondCertificate cert hk hs)) := by
  rintro _ ⟨r, rfl⟩ _ ⟨t, rfl⟩ hne
  simp only [secondCertificate_apply]
  generalize hr : outerIndexEquiv hs r = ir
  generalize ht : outerIndexEquiv hs t = it
  cases ir with
  | none =>
      cases it with
      | none =>
          exact False.elim (hne (by
            simp [secondCertificate_apply, hr, ht, secondCertificateAt]))
      | some q =>
          simp only [secondCertificateAt]
          rw [(specialLift G cert.c)ᶜ.adj_comm]
          rw [specialLift_compl_adj_core_a]
          exact cert.c_ne_i (Certificates.c0Index hk) q
  | some p =>
      cases it with
      | none =>
          simp only [secondCertificateAt]
          rw [specialLift_compl_adj_core_a]
          exact cert.c_ne_i (Certificates.c0Index hk) p
      | some q =>
          simp only [secondCertificateAt]
          rw [specialLift_compl_adj_core_core]
          apply cert.i_compl_adj
          intro hpq
          subst q
          exact hne (by
            simp [secondCertificate_apply, hr, ht, secondCertificateAt])

/-- Vertices after both standard lifts, before the clone is added. -/
abbrev Vertex (V : Type*) (k s : ℕ) :=
  SpecialLiftVertex (SpecialLiftVertex V k) (s + 1)

/-- The graph `F` of Section 2: first lift, complementary second lift,
then complement back to the original red/blue convention. -/
def graph (G : SimpleGraph V) (cert : Certificates G k s)
    (hk : 5 ≤ k) (hs : 1 ≤ s) : SimpleGraph (Vertex V k s) :=
  (specialLift (specialLift G cert.c)ᶜ
    (secondCertificate cert hk hs))ᶜ

/-- Both standard lifts preserve the required Ramsey-freeness. -/
theorem graph_isRamseyFree
    (cert : Certificates G k s) (hk : 5 ≤ k) (hs5 : 5 ≤ s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree
      (graph G cert hk
        (le_trans (by decide : 1 ≤ 5) hs5))
      (k + 1) (s + 1) := by
  have hs : 1 ≤ s := le_trans (by decide : 1 ≤ 5) hs5
  have hsSucc : 5 ≤ s + 1 := le_trans hs5 (Nat.le_succ s)
  have hfirst :
      IsRamseyFree (specialLift G cert.c) k (s + 1) :=
    specialLift_isRamseyFree G cert.c cert.c_isClique hk hG
  have hsecond :=
    specialLift_isRamseyFree (k := s + 1) (s := k)
      (specialLift G cert.c)ᶜ
      (secondCertificate cert hk hs)
      (secondCertificate_isClique cert hk hs)
      hsSucc hfirst.symm
  simpa [graph] using hsecond.symm

@[simp]
theorem card_vertex [Fintype V] :
    Fintype.card (Vertex V k s) =
      Fintype.card V + 2 * (k - 1) + 2 * s := by
  rw [SpecialLiftVertex.card, SpecialLiftVertex.card]
  omega

end Canonical
end RamseyIncrement
