/-
R(12,12) ≥ 1642.
-/
import RamseyIncrement.R1212.Mathon
import RamseyIncrement.R1212.PaleyClique
import RamseyIncrement.ThirdConnector.Theorem
import RamseyIncrement.RamseyNumber

/-!
# `R(12,12) ≥ 1642`

Apply the rule R* (`ThirdConnector.rstar_isRamseyFree`) to the Mathon graph
`M(797)` with the certificates of Appendix A of the report:

* `C = (B₁₃₃, B₁₂₉, B₇₇₆, B₅₄₁, B₆₈₂, B₆₈₆, B₆₉₅, B₇₈₅, B₇₈₉, b)`, a red `K₁₀`;
* `I = (B₂₆₄, B₇₉₁, B₇₇₉, B₇₅₂, B₇₅₇, a, B₆₇₅, B₇₆₀, B₂₈₂, B₄₇₀)`, a blue `K₁₀`.

They are Type A with `P = {2}` (P1), and `c₂` is red to `i₃` (P2).  The result is
a `(12,12)`-coloring on `1596 + 22 + 22 + 1 = 1641` vertices.
-/

namespace RamseyIncrement
namespace R1212

open MV

/-- The red certificate `C`. -/
def cVec : Fin 10 → MV :=
  ![B 133, B 129, B 776, B 541, B 682, B 686, B 695, B 785, B 789, b]

/-- The blue certificate `I`. -/
def iVec : Fin 10 → MV :=
  ![B 264, B 791, B 779, B 752, B 757, a, B 675, B 760, B 282, B 470]

theorem cVec_injective : Function.Injective cVec := by decide
theorem iVec_injective : Function.Injective iVec := by decide

theorem cVec_clique : ∀ p q : Fin 10, p ≠ q → mathon.Adj (cVec p) (cVec q) := by
  decide +kernel

theorem iVec_coclique : ∀ p q : Fin 10, p ≠ q → ¬mathon.Adj (iVec p) (iVec q) := by
  decide +kernel

theorem cVec_ne_iVec : ∀ p q : Fin 10, cVec p ≠ iVec q := by decide

/-- The incidence matrix, column by column: `c₁` is red to `i_q`, or some other
`c_p` is blue to it.  So no `β(i_q)` equals `{1}`. -/
theorem not_unique_c1 : ∀ q : Fin 10, mathon.Adj (cVec 1) (iVec q) ∨
    ∃ p : Fin 10, p ≠ 1 ∧ ¬mathon.Adj (cVec p) (iVec q) := by
  decide +kernel

/-- Column `i₀` is blue exactly in row `c₂`. -/
theorem col_i0 : ∀ p : Fin 10, ¬mathon.Adj (cVec p) (iVec 0) ↔ p = 2 := by decide +kernel

theorem c2_i3 : mathon.Adj (cVec 2) (iVec 3) := by decide +kernel

def certs : Certificates mathon 11 11 where
  c := ⟨cVec, cVec_injective⟩
  i := ⟨iVec, iVec_injective⟩
  c_isClique := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    exact cVec_clique p q (fun h ↦ hpq (by rw [h]))
  i_isClique := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    exact (SimpleGraph.compl_adj _ _ _).2 ⟨hpq, iVec_coclique p q (fun h ↦ hpq (by rw [h]))⟩
  disjoint := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    exact cVec_ne_iVec p q hq.symm

theorem certs_caseA : certs.IsCaseA (by norm_num) (by norm_num) := by
  refine ⟨fun q h ↦ ?_, ?_⟩
  · rw [Certificates.isUniqueBlueWitness_iff] at h
    rcases not_unique_c1 q with hred | ⟨p, hp1, hpb⟩
    · have : Certificates.c1Index (k := 11) (by norm_num) ∈ certs.beta q := by
        rw [h]
        exact Finset.mem_singleton_self _
      rw [Certificates.mem_beta] at this
      exact this hred
    · have : p ∈ certs.beta q := (Certificates.mem_beta _ _ _).2 hpb
      rw [h, Finset.mem_singleton] at this
      exact hp1 this
  · exact not_not.1 ((col_i0 0).not.2 (by decide))

def ocerts : Certificates.OrderedCertificates mathon 11 11 :=
  { certs with
    five_le_k := by norm_num
    five_le_s := by norm_num
    normal := .caseA certs_caseA }

def data797 : Certificates.PlusCaseAData mathon 11 11 where
  cert := ocerts
  isPlusA := ⟨certs_caseA, not_not.1 ((col_i0 1).not.2 (by decide)),
    (col_i0 2).2 rfl⟩

theorem data797_P1 : ThirdConnector.P1 data797 := by
  ext p
  rw [Finset.mem_singleton]
  change p ∈ certs.beta _ ↔ _
  rw [Certificates.mem_beta]
  exact col_i0 p

theorem data797_P2 : ThirdConnector.P2 data797 :=
  ⟨3, by decide, c2_i3⟩

/-- `M(797)` is an `(11,11)`-coloring. -/
theorem mathon797_isRamseyFree : IsRamseyFree mathon 11 11 :=
  mathon_isRamseyFree paley_cliqueFree

/-- A `(12,12)`-coloring on `1641` vertices. -/
theorem r1212_hasRamseyColoring : HasRamseyColoring 1641 12 12 := by
  have h := ThirdConnector.rstar_isRamseyFree data797 data797_P1 data797_P2
    mathon797_isRamseyFree
  have hcard : Fintype.card (ThirdConnector.Vertex MV 11 11) = 1641 := by
    rw [ThirdConnector.card_vertex data797, card_MV]
  exact ⟨_, h.overFin hcard⟩

/-- **`R(12,12) ≥ 1642`.** -/
theorem r1212_lower_bound : 1642 ≤ ramseyNumber 12 12 :=
  ramseyNumber_lower_bound r1212_hasRamseyColoring

end R1212
end RamseyIncrement
