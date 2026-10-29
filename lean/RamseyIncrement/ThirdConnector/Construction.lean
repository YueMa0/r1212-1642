/-
Rule R*: a third connector for the Type A construction.
Added on top of Tatarevic's development; the original files are unchanged.
-/
import RamseyIncrement.SecondConnector.TypeA.Theorem

/-!
# The rule R* (construction)

Start from the Type A output `H⁺ = plusGraphA data`.  Switch the old edges
`c₂x₀` and `i₀x_*` from red to blue and `a_p y₀` (`p` odd) from blue to red,
then adjoin a vertex `u` with the red neighborhood `redToU`:

* red to `C`, `i₀`, `a_p` (`p` even), `b_p` (`p ≠ 2`), `x₀`, `x_*`, `y_*`;
* blue to the rest of `I`, `a_p` (`p` odd), `b₂`, the other `x` and `y`, `z`, `w`;
* the color of `i₀` on the remaining core vertices.

This is Section 2 of `02_expert_report.md`.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-- Vertices of `H⁺` together with the third connector `u`. -/
abbrev Vertex (V : Type*) (k s : ℕ) :=
  SecondConnector.AdjoinVertex (SecondConnector.Vertex V k s)

/-! ## Named vertices of `H⁺` -/

/-- The vertex of `H⁺` coming from a vertex of `G`. -/
abbrev core (v : V) : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old (Switching.Vertex.core v)

abbrev a (p : Fin (k - 1)) : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old (Switching.Vertex.a p)

abbrev b (p : Fin (k - 1)) : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old (Switching.Vertex.b p)

abbrev x (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old (Switching.Vertex.x cert r)

abbrev y (cert : Certificates.OrderedCertificates G k s)
    (r : Option (Fin (s - 1))) : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old (Switching.Vertex.y cert r)

abbrev z : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.old Switching.Vertex.z

abbrev w : SecondConnector.Vertex V k s :=
  SecondConnector.Vertex.w

/-! ## The hypotheses (P1) and (P2) -/

/-- (P1): `P = {2}`, i.e. `i₀` is blue to `c₂` and red to the rest of `C`. -/
def P1 (data : Certificates.PlusCaseAData G k s) : Prop :=
  SecondConnector.TypeA.P data = {SecondConnector.TypeA.c2Index data}

/-- (P2): `c₂` is red to some `i_r` with `2 ≤ r ≤ s-2`. -/
def P2 (data : Certificates.PlusCaseAData G k s) : Prop :=
  ∃ r : Fin (s - 1), 2 ≤ r.val ∧
    G.Adj (data.cert.c (SecondConnector.TypeA.c2Index data)) (data.cert.i r)

/-! ## The switched edges -/

/-- The edges of `H⁺` switched from red to blue: `c₂x₀` and `i₀x_*`. -/
def removedRedRel (data : Certificates.PlusCaseAData G k s) :
    SecondConnector.Vertex V k s → SecondConnector.Vertex V k s → Prop :=
  fun u v ↦
    Switching.SymmPair
        (core (data.cert.c (SecondConnector.TypeA.c2Index data)))
        (x data.cert (some (SecondConnector.TypeA.i0Index data))) u v ∨
      Switching.SymmPair
        (core (data.cert.i (SecondConnector.TypeA.i0Index data)))
        (x data.cert none) u v

/-- The edges of `H⁺` switched from blue to red: `a_p y₀` for odd `p`. -/
def addedRedRel (data : Certificates.PlusCaseAData G k s) :
    SecondConnector.Vertex V k s → SecondConnector.Vertex V k s → Prop :=
  fun u v ↦
    ∃ p : Fin (k - 1), p.val % 2 = 1 ∧
      Switching.SymmPair (a p)
        (y data.cert (some (SecondConnector.TypeA.i0Index data))) u v

def removedRedGraph (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (SecondConnector.Vertex V k s) :=
  SimpleGraph.fromRel (removedRedRel data)

def addedRedGraph (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (SecondConnector.Vertex V k s) :=
  SimpleGraph.fromRel (addedRedRel data)

/-- `H⁺` after the switches of R*. -/
noncomputable def oldGraph (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (SecondConnector.Vertex V k s) :=
  (SecondConnector.TypeA.plusGraphA data \ removedRedGraph data) ⊔
    addedRedGraph data

theorem oldGraph_adj_iff (data : Certificates.PlusCaseAData G k s)
    (u v : SecondConnector.Vertex V k s) :
    (oldGraph data).Adj u v ↔
      (SecondConnector.TypeA.plusGraphA data).Adj u v ∧
          ¬(removedRedGraph data).Adj u v ∨
        (addedRedGraph data).Adj u v :=
  Iff.rfl

/-! ## The third connector -/

/-- The red neighborhood of `u` among the vertices of `H⁺`. -/
noncomputable def redToU (data : Certificates.PlusCaseAData G k s) :
    SecondConnector.Vertex V k s → Prop
  | .inl (.inl (.core (.core v))) =>
      (∃ p, v = data.cert.c p) ∨
        v = data.cert.i (SecondConnector.TypeA.i0Index data) ∨
        G.Adj (data.cert.i (SecondConnector.TypeA.i0Index data)) v
  | .inl (.inl (.core (.a p))) => p.val % 2 = 0
  | .inl (.inl (.core (.b p))) => p ≠ SecondConnector.TypeA.c2Index data
  | .inl (.inl (.a r)) =>
      let q := Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r
      q = none ∨ q = some (SecondConnector.TypeA.i0Index data)
  | .inl (.inl (.b r)) =>
      Canonical.outerIndexEquiv
        (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r = none
  | .inl (.inr _) => False
  | .inr _ => False

/-- The coloring `O` of R*. -/
noncomputable def rstarGraph (data : Certificates.PlusCaseAData G k s) :
    SimpleGraph (Vertex V k s) :=
  SecondConnector.adjoinWithRedNeighborhood (oldGraph data) (redToU data)

section redToU

variable (data : Certificates.PlusCaseAData G k s)

@[simp]
theorem redToU_core (v : V) :
    redToU data (core v) ↔
      (∃ p, v = data.cert.c p) ∨
        v = data.cert.i (SecondConnector.TypeA.i0Index data) ∨
        G.Adj (data.cert.i (SecondConnector.TypeA.i0Index data)) v :=
  Iff.rfl

@[simp]
theorem redToU_a (p : Fin (k - 1)) :
    redToU data (a p) ↔ p.val % 2 = 0 :=
  Iff.rfl

@[simp]
theorem redToU_b (p : Fin (k - 1)) :
    redToU data (b p) ↔ p ≠ SecondConnector.TypeA.c2Index data :=
  Iff.rfl

@[simp]
theorem redToU_x (r : Option (Fin (s - 1))) :
    redToU data (x data.cert r) ↔
      r = none ∨ r = some (SecondConnector.TypeA.i0Index data) := by
  simp [redToU]

@[simp]
theorem redToU_y (r : Option (Fin (s - 1))) :
    redToU data (y data.cert r) ↔ r = none := by
  simp [redToU]

@[simp]
theorem redToU_z : ¬redToU data (z : SecondConnector.Vertex V k s) :=
  id

@[simp]
theorem redToU_w : ¬redToU data (w : SecondConnector.Vertex V k s) :=
  id

end redToU

/-- `O` has `|V| + 2k + 2s + 1` vertices. -/
@[simp]
theorem card_vertex [Fintype V] (data : Certificates.PlusCaseAData G k s) :
    Fintype.card (Vertex V k s) = Fintype.card V + 2 * k + 2 * s + 1 := by
  rw [SecondConnector.card_adjoinVertex, SecondConnector.card_plusVertex data.cert]

end ThirdConnector
end RamseyIncrement
