/-
Rule R*: the colour table of the switched graph (Section 3 of the report).
-/
import RamseyIncrement.ThirdConnector.Construction
import RamseyIncrement.SecondConnector.TypeA.ChangedEdges

/-!
# Colour table of `oldGraph`

Red adjacency in `H⁺` after the switches of R*, between the named vertices.
Each right-hand side is the entry of Section 3 of `02_expert_report.md`, so
these lemmas check the table against the definitions.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private theorem fromRel_adj_iff_of_symm {α : Type*} (R : α → α → Prop)
    (hsymm : ∀ u v, R u v ↔ R v u) (hne : ∀ ⦃u v⦄, R u v → u ≠ v) (u v : α) :
    (SimpleGraph.fromRel R).Adj u v ↔ R u v := by
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact (hsymm v u).1 h
  · intro h
    exact ⟨hne h, Or.inl h⟩

set_option hygiene false in
/-- Unfold red adjacency of `oldGraph` between old vertices to the source
colors of the canonical lifts and the three lists of switches. -/
macro "rstar_colour" : tactic => `(tactic| (
  rw [old_adj_old_iff, Switching.final_adj_iff]
  simp [removedRedRel, addedRedRel, Switching.SymmPair,
    Switching.removedRedGraph_adj_iff, Switching.addedRedGraph_adj_iff,
    SecondConnector.TypeA.extraARemovedRedRel, SecondConnector.TypeA.extraAAddedRedRel,
    Switching.preGraph_adj_y_y_iff, Switching.preGraph_not_adj_x_x,
    Switching.preGraph_adj_x_y_iff, Canonical.secondCertificateAt, SameBPart,
    Certificates.c_ne_i, SecondConnector.TypeA.c0Index, SecondConnector.TypeA.c2Index,
    SecondConnector.TypeA.i0Index, SecondConnector.TypeA.i2Index, Switching.Vertex.c0,
    Switching.Vertex.c2, Switching.Vertex.i1, Switching.outerIndexEquiv_symm_some_val,
    Switching.outerIndexEquiv_symm_none_val]))

set_option hygiene false in
/-- The `simp` half of `rstar_colour`, for goals already unfolded by hand. -/
macro "rstar_colour'" : tactic => `(tactic| (
  simp [removedRedRel, addedRedRel, Switching.SymmPair,
    Switching.removedRedGraph_adj_iff, Switching.addedRedGraph_adj_iff,
    SecondConnector.TypeA.extraARemovedRedRel, SecondConnector.TypeA.extraAAddedRedRel,
    Switching.preGraph_adj_y_y_iff, Switching.preGraph_not_adj_x_x,
    Switching.preGraph_adj_x_y_iff, Canonical.secondCertificateAt, SameBPart,
    Certificates.c_ne_i, SecondConnector.TypeA.c0Index, SecondConnector.TypeA.c2Index,
    SecondConnector.TypeA.i0Index, SecondConnector.TypeA.i2Index, Switching.Vertex.c0,
    Switching.Vertex.c2, Switching.Vertex.i1, Switching.outerIndexEquiv_symm_some_val,
    Switching.outerIndexEquiv_symm_none_val]))

section

variable (data : Certificates.PlusCaseAData G k s)

@[simp]
theorem removedRedGraph_adj_iff (u v : SecondConnector.Vertex V k s) :
    (removedRedGraph data).Adj u v ↔ removedRedRel data u v := by
  apply fromRel_adj_iff_of_symm
  · intro u v
    simp only [removedRedRel, Switching.symmPair_comm]
  · intro u v h
    rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

@[simp]
theorem addedRedGraph_adj_iff (u v : SecondConnector.Vertex V k s) :
    (addedRedGraph data).Adj u v ↔ addedRedRel data u v := by
  apply fromRel_adj_iff_of_symm
  · intro u v
    simp only [addedRedRel, Switching.symmPair_comm]
  · intro u v h
    obtain ⟨p, _, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Unfold red adjacency of `oldGraph` between two old vertices of `H⁺`
down to the first-connector graph. -/
theorem old_adj_old_iff (u v : Switching.Vertex V k s) :
    (oldGraph data).Adj (SecondConnector.Vertex.old u) (SecondConnector.Vertex.old v) ↔
      (((Switching.finalGraph data.cert).Adj u v ∧
          ¬SecondConnector.TypeA.extraARemovedRedRel data u v ∨
        SecondConnector.TypeA.extraAAddedRedRel data u v) ∧
          ¬removedRedRel data (SecondConnector.Vertex.old u) (SecondConnector.Vertex.old v)) ∨
        addedRedRel data (SecondConnector.Vertex.old u) (SecondConnector.Vertex.old v) := by
  rw [oldGraph_adj_iff, removedRedGraph_adj_iff, addedRedGraph_adj_iff,
    SecondConnector.TypeA.plusGraphA_adj_old_old,
    SecondConnector.TypeA.extraAOldGraph_adj_iff]

/-- The switches of R* do not touch `w`. -/
@[simp]
theorem old_adj_old_w (v : Switching.Vertex V k s) :
    (oldGraph data).Adj (SecondConnector.Vertex.old v) w ↔
      SecondConnector.TypeA.redToWA data v := by
  rw [oldGraph_adj_iff, removedRedGraph_adj_iff, addedRedGraph_adj_iff]
  simp [removedRedRel, addedRedRel, Switching.SymmPair]

/-! ## Core vertices against everything -/

@[simp]
theorem old_adj_core_core (v v' : V) :
    (oldGraph data).Adj (core v) (core v') ↔ G.Adj v v' := by
  rw [old_adj_old_iff, Switching.final_adj_iff]
  simp [removedRedRel, addedRedRel, Switching.SymmPair,
    Switching.removedRedGraph_adj_iff, Switching.addedRedGraph_adj_iff,
    SecondConnector.TypeA.extraARemovedRedRel, SecondConnector.TypeA.extraAAddedRedRel]

@[simp]
theorem old_adj_a_core (p : Fin (k - 1)) (v : V) :
    (oldGraph data).Adj (a p) (core v) ↔
      data.cert.c p = v ∨ (p = c2Index data ∧ v = data.cert.i (i0Index data)) := by
  rw [old_adj_old_iff, Switching.final_adj_iff]
  simp [removedRedRel, addedRedRel, Switching.SymmPair,
    Switching.removedRedGraph_adj_iff, Switching.addedRedGraph_adj_iff,
    SecondConnector.TypeA.extraARemovedRedRel, SecondConnector.TypeA.extraAAddedRedRel]

@[simp]
theorem old_adj_b_core (p : Fin (k - 1)) (v : V) :
    (oldGraph data).Adj (b p) (core v) ↔ v ≠ data.cert.c p ∧ G.Adj (data.cert.c p) v := by
  rstar_colour

@[simp]
theorem old_adj_a_a (p p' : Fin (k - 1)) :
    (oldGraph data).Adj (a p) (a p') ↔ p ≠ p' := by
  rstar_colour

@[simp]
theorem old_adj_a_b (p p' : Fin (k - 1)) :
    (oldGraph data).Adj (a p) (b p') ↔ p ≠ p' := by
  rstar_colour

/-- `B` is red inside the blocks `{b₀,b₁}`, `{b₂,…}`, blue between them,
except `b₀b₂`, which is red. -/
@[simp]
theorem old_adj_b_b (p p' : Fin (k - 1)) :
    (oldGraph data).Adj (b p) (b p') ↔
      (p ≠ p' ∧ SameBPart p p') ∨ (p = c0Index data ∧ p' = c2Index data) ∨
        (p = c2Index data ∧ p' = c0Index data) := by
  rstar_colour

/-- `x_q` is blue only to `i_q`; `x₀` is also blue to `c₂` (switch of R*). -/
@[simp]
theorem old_adj_core_x_some (v : V) (q : Fin (s - 1)) :
    (oldGraph data).Adj (core v) (x data.cert (some q)) ↔
      data.cert.i q ≠ v ∧ (v = data.cert.c (c2Index data) → q ≠ i0Index data) := by
  rstar_colour

/-- `x_*` is blue only to `c_p` (`p ∈ P`) and to `i₀` (switch of R*). -/
@[simp]
theorem old_adj_core_x_none (v : V) :
    (oldGraph data).Adj (core v) (x data.cert none) ↔
      (∀ p ∈ P data, v ≠ data.cert.c p) ∧ v ≠ data.cert.i (i0Index data) := by
  rstar_colour

/-- `A`–`X` is red except `a₀x_*`. -/
@[simp]
theorem old_adj_a_x (hE : data.cert.E = ∅) (p : Fin (k - 1)) (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj (a p) (x data.cert r) ↔ ¬(p = c0Index data ∧ r = none) := by
  cases r <;> rw [old_adj_old_iff, Switching.final_adj_iff] <;>
    simp [removedRedRel, addedRedRel, Switching.SymmPair, Switching.removedRedGraph_adj_iff,
      Switching.addedRedGraph_adj_iff, SecondConnector.TypeA.extraARemovedRedRel,
      SecondConnector.TypeA.extraAAddedRedRel, Canonical.secondCertificateAt, hE,
      SecondConnector.TypeA.c0Index, Switching.Vertex.c0, eq_comm]

/-- `B`–`X` is red except `b₀x₁` and `b₀x_*`. -/
@[simp]
theorem old_adj_b_x (p : Fin (k - 1)) (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj (b p) (x data.cert r) ↔
      ¬(p = c0Index data ∧ (r = some (Switching.Vertex.i1 data.cert) ∨ r = none)) := by
  cases r <;> rstar_colour

/-- `y_q` is red to `i_q` and copies `i_q` on the rest of `V`. -/
@[simp]
theorem old_adj_core_y_some (v : V) (q : Fin (s - 1)) :
    (oldGraph data).Adj (core v) (y data.cert (some q)) ↔
      v = data.cert.i q ∨ G.Adj (data.cert.i q) v := by
  rstar_colour

/-- `y_*` is red only to `c₀`. -/
@[simp]
theorem old_adj_core_y_none (v : V) :
    (oldGraph data).Adj (core v) (y data.cert none) ↔ data.cert.c (c0Index data) = v := by
  rstar_colour

/-- `a_p y_q` is blue except `a₀y_q` (`q ∈ T`) and `a_p y₀` (`p` odd, R*). -/
@[simp]
theorem old_adj_a_y_some (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (oldGraph data).Adj (a p) (y data.cert (some q)) ↔
      (q ∈ data.cert.T ∧ p = c0Index data) ∨ (p.val % 2 = 1 ∧ q = i0Index data) := by
  rstar_colour

@[simp]
theorem old_adj_a_y_none (p : Fin (k - 1)) :
    (oldGraph data).Adj (a p) (y data.cert none) := by
  rstar_colour
  exact (em _).imp_right fun h h' ↦ h h'.symm

/-- `b₀y_q` is blue; for `p ≠ 0`, `b_p y_q` has the color of `c_p i_q`. -/
@[simp]
theorem old_adj_b_y_some (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (oldGraph data).Adj (b p) (y data.cert (some q)) ↔
      p ≠ c0Index data ∧ G.Adj (data.cert.c p) (data.cert.i q) := by
  rstar_colour
  constructor
  · rintro ⟨⟨_, h⟩, h0⟩
    refine ⟨fun hp ↦ ?_, h⟩
    subst hp
    exact h0 h rfl
  · rintro ⟨hp, h⟩
    exact ⟨⟨fun h' ↦ data.cert.c_ne_i p q h'.symm, h⟩, fun _ ↦ hp⟩

@[simp]
theorem old_adj_b_y_none (p : Fin (k - 1)) :
    (oldGraph data).Adj (b p) (y data.cert none) := by
  rstar_colour
  exact (em _).symm.imp_left fun h h' ↦ h h'.symm

@[simp]
theorem old_not_adj_x_x (r t : Option (Fin (s - 1))) :
    ¬(oldGraph data).Adj (x data.cert r) (x data.cert t) := by
  rstar_colour

@[simp]
theorem old_adj_x_y (r t : Option (Fin (s - 1))) :
    (oldGraph data).Adj (x data.cert r) (y data.cert t) ↔ r = t := by
  rstar_colour

/-- The low `Y` block `{y₀, y₁}`. -/
def YLow : Option (Fin (s - 1)) → Prop
  | some q => q.val < 2
  | none => False

/-- `Y` is blue inside the blocks `{y₀,y₁}`, `{y₂,…,y_*}` and red between
them, except `y₀y₂` and `y₀y_*`, which are blue. -/
@[simp]
theorem old_adj_y_y (hE : data.cert.E = ∅) (r t : Option (Fin (s - 1))) :
    (oldGraph data).Adj (y data.cert r) (y data.cert t) ↔
      r ≠ t ∧ (YLow r ↔ ¬YLow t) ∧
        ¬Switching.SymmPair (some (i0Index data)) none r t ∧
        ¬Switching.SymmPair (some (i0Index data)) (some (i2Index data)) r t := by
  have hs := data.cert.five_le_s
  cases r <;> cases t <;> rw [old_adj_old_iff, Switching.final_adj_iff] <;>
    simp [removedRedRel, addedRedRel, Switching.SymmPair, Switching.removedRedGraph_adj_iff,
      Switching.addedRedGraph_adj_iff, SecondConnector.TypeA.extraARemovedRedRel,
      SecondConnector.TypeA.extraAAddedRedRel, Switching.preGraph_adj_y_y_iff, SameBPart,
      Switching.outerIndexEquiv_symm_some_val, Switching.outerIndexEquiv_symm_none_val, hE,
      YLow] <;> omega

/-! ## The first connector `z` -/

/-- In the first-connector graph, `z` is a red-joined clone of `b₀`. -/
theorem pre_adj_old_z (u : Canonical.Vertex V k s) :
    (Switching.preGraph data.cert).Adj (.inl u) Switching.Vertex.z ↔
      u = .core (.b (Switching.Vertex.c0 data.cert)) ∨
        (Switching.preGraph data.cert).Adj (.inl u)
          (Switching.Vertex.b (Switching.Vertex.c0 data.cert)) :=
  Iff.rfl

theorem pre_adj_x_b (r : Option (Fin (s - 1))) (p : Fin (k - 1)) :
    (Switching.preGraph data.cert).Adj (Switching.Vertex.x data.cert r) (Switching.Vertex.b p) ↔
      Canonical.secondCertificateAt data.cert.toCertificates data.cert.five_le_k r ≠ .b p := by
  rw [SimpleGraph.adj_comm]
  exact Switching.preGraph_adj_lower_x_iff data.cert (.b p) r

theorem pre_adj_y_b (r : Option (Fin (s - 1))) (p : Fin (k - 1)) :
    (Switching.preGraph data.cert).Adj (Switching.Vertex.y data.cert r) (Switching.Vertex.b p) ↔
      .b p = Canonical.secondCertificateAt data.cert.toCertificates data.cert.five_le_k r ∨
        (specialLift G data.cert.c).Adj
          (Canonical.secondCertificateAt data.cert.toCertificates data.cert.five_le_k r) (.b p) := by
  rw [SimpleGraph.adj_comm]
  exact Switching.preGraph_adj_lower_y_iff data.cert (.b p) r

/-- `z` is blue to `c₀` and copies `c₀` on the rest of `V`. -/
@[simp]
theorem old_adj_core_z (v : V) :
    (oldGraph data).Adj (core v) z ↔
      v ≠ data.cert.c (c0Index data) ∧ G.Adj (data.cert.c (c0Index data)) v := by
  rw [old_adj_old_iff, Switching.final_adj_iff, pre_adj_old_z]
  rstar_colour'

@[simp]
theorem old_adj_a_z (p : Fin (k - 1)) :
    (oldGraph data).Adj (a p) z ↔ p ≠ c0Index data := by
  rw [old_adj_old_iff, Switching.final_adj_iff, pre_adj_old_z]
  rstar_colour'

/-- `b_p z` is red exactly for `p ∈ {0, 1}`. -/
@[simp]
theorem old_adj_b_z (p : Fin (k - 1)) :
    (oldGraph data).Adj (b p) z ↔ p.val < 2 := by
  rw [old_adj_old_iff, Switching.final_adj_iff, pre_adj_old_z]
  rstar_colour'
  constructor
  · rintro (h | ⟨_, h⟩)
    · subst h
      simp [Certificates.c0Index]
    · omega
  · intro h
    by_cases h0 : p.val = 0
    · left
      exact Fin.ext (by simpa [Certificates.c0Index] using h0)
    · right
      exact ⟨fun h' ↦ h0 (by simpa [Certificates.c0Index] using congrArg Fin.val h'), by omega⟩

/-- `x_r z` is red exactly for `r ∈ {1, *}`. -/
@[simp]
theorem old_adj_x_z (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj (x data.cert r) z ↔
      r = some (Switching.Vertex.i1 data.cert) ∨ r = none := by
  rw [old_adj_old_iff, Switching.final_adj_iff, pre_adj_old_z, pre_adj_x_b]
  cases r <;> rstar_colour'

/-- `y_r z` is red exactly for `r ∈ T`; `y_* z` is blue. -/
@[simp]
theorem old_adj_y_z (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj (y data.cert r) z ↔ ∃ q ∈ data.cert.T, r = some q := by
  rw [old_adj_old_iff, Switching.final_adj_iff, pre_adj_old_z, pre_adj_y_b]
  cases r <;> rstar_colour'
  exact fun _ h ↦ data.cert.c_ne_i _ _ h.symm

/-! ## The same entries with the arguments swapped -/

@[simp] theorem old_adj_w_old (v : Switching.Vertex V k s) :
    (oldGraph data).Adj w (SecondConnector.Vertex.old v) ↔
      SecondConnector.TypeA.redToWA data v := by
  rw [SimpleGraph.adj_comm, old_adj_old_w]

@[simp] theorem old_adj_core_a (v : V) (p : Fin (k - 1)) :
    (oldGraph data).Adj (core v) (a p) ↔
      data.cert.c p = v ∨ (p = c2Index data ∧ v = data.cert.i (i0Index data)) := by
  rw [SimpleGraph.adj_comm, old_adj_a_core]

@[simp] theorem old_adj_core_b (v : V) (p : Fin (k - 1)) :
    (oldGraph data).Adj (core v) (b p) ↔ v ≠ data.cert.c p ∧ G.Adj (data.cert.c p) v := by
  rw [SimpleGraph.adj_comm, old_adj_b_core]

@[simp] theorem old_adj_b_a (p p' : Fin (k - 1)) :
    (oldGraph data).Adj (b p) (a p') ↔ p' ≠ p := by
  rw [SimpleGraph.adj_comm, old_adj_a_b]

@[simp] theorem old_adj_x_core_some (q : Fin (s - 1)) (v : V) :
    (oldGraph data).Adj (x data.cert (some q)) (core v) ↔
      data.cert.i q ≠ v ∧ (v = data.cert.c (c2Index data) → q ≠ i0Index data) := by
  rw [SimpleGraph.adj_comm, old_adj_core_x_some]

@[simp] theorem old_adj_x_core_none (v : V) :
    (oldGraph data).Adj (x data.cert none) (core v) ↔
      (∀ p ∈ P data, v ≠ data.cert.c p) ∧ v ≠ data.cert.i (i0Index data) := by
  rw [SimpleGraph.adj_comm, old_adj_core_x_none]

@[simp] theorem old_adj_x_a (hE : data.cert.E = ∅) (r : Option (Fin (s - 1))) (p : Fin (k - 1)) :
    (oldGraph data).Adj (x data.cert r) (a p) ↔ ¬(p = c0Index data ∧ r = none) := by
  rw [SimpleGraph.adj_comm, old_adj_a_x data hE]

@[simp] theorem old_adj_x_b (r : Option (Fin (s - 1))) (p : Fin (k - 1)) :
    (oldGraph data).Adj (x data.cert r) (b p) ↔
      ¬(p = c0Index data ∧ (r = some (Switching.Vertex.i1 data.cert) ∨ r = none)) := by
  rw [SimpleGraph.adj_comm, old_adj_b_x]

@[simp] theorem old_adj_y_core_some (q : Fin (s - 1)) (v : V) :
    (oldGraph data).Adj (y data.cert (some q)) (core v) ↔
      v = data.cert.i q ∨ G.Adj (data.cert.i q) v := by
  rw [SimpleGraph.adj_comm, old_adj_core_y_some]

@[simp] theorem old_adj_y_core_none (v : V) :
    (oldGraph data).Adj (y data.cert none) (core v) ↔ data.cert.c (c0Index data) = v := by
  rw [SimpleGraph.adj_comm, old_adj_core_y_none]

@[simp] theorem old_adj_y_a_some (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (oldGraph data).Adj (y data.cert (some q)) (a p) ↔
      (q ∈ data.cert.T ∧ p = c0Index data) ∨ (p.val % 2 = 1 ∧ q = i0Index data) := by
  rw [SimpleGraph.adj_comm, old_adj_a_y_some]

@[simp] theorem old_adj_y_a_none (p : Fin (k - 1)) :
    (oldGraph data).Adj (y data.cert none) (a p) := by
  rw [SimpleGraph.adj_comm]
  exact old_adj_a_y_none data p

@[simp] theorem old_adj_y_b_some (q : Fin (s - 1)) (p : Fin (k - 1)) :
    (oldGraph data).Adj (y data.cert (some q)) (b p) ↔
      p ≠ c0Index data ∧ G.Adj (data.cert.c p) (data.cert.i q) := by
  rw [SimpleGraph.adj_comm, old_adj_b_y_some]

@[simp] theorem old_adj_y_b_none (p : Fin (k - 1)) :
    (oldGraph data).Adj (y data.cert none) (b p) := by
  rw [SimpleGraph.adj_comm]
  exact old_adj_b_y_none data p

@[simp] theorem old_adj_y_x (t r : Option (Fin (s - 1))) :
    (oldGraph data).Adj (y data.cert t) (x data.cert r) ↔ r = t := by
  rw [SimpleGraph.adj_comm, old_adj_x_y]

@[simp] theorem old_adj_z_core (v : V) :
    (oldGraph data).Adj z (core v) ↔
      v ≠ data.cert.c (c0Index data) ∧ G.Adj (data.cert.c (c0Index data)) v := by
  rw [SimpleGraph.adj_comm, old_adj_core_z]

@[simp] theorem old_adj_z_a (p : Fin (k - 1)) :
    (oldGraph data).Adj z (a p) ↔ p ≠ c0Index data := by
  rw [SimpleGraph.adj_comm, old_adj_a_z]

@[simp] theorem old_adj_z_b (p : Fin (k - 1)) :
    (oldGraph data).Adj z (b p) ↔ p.val < 2 := by
  rw [SimpleGraph.adj_comm, old_adj_b_z]

@[simp] theorem old_adj_z_x (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj z (x data.cert r) ↔
      r = some (Switching.Vertex.i1 data.cert) ∨ r = none := by
  rw [SimpleGraph.adj_comm, old_adj_x_z]

@[simp] theorem old_adj_z_y (r : Option (Fin (s - 1))) :
    (oldGraph data).Adj z (y data.cert r) ↔ ∃ q ∈ data.cert.T, r = some q := by
  rw [SimpleGraph.adj_comm, old_adj_y_z]

end

end ThirdConnector
end RamseyIncrement
