/-
Rule R*, Part II: no red `K_k` in the red neighborhood of `u`.
-/
import RamseyIncrement.ThirdConnector.BlueU

/-!
# Part II: red cliques through `u`

The red neighborhood of `u` is `C ∪ {i₀} ∪ G₀`, the even `a_p`, the `b_p` with
`p ≠ 2`, and `x₀, x_*, y_*`.  Let `K` be a red clique in it.

* No `a` and no `y_*` (II.1): project to a red clique of `G` by
  core `g ↦ g`, `b_q ↦ c_q`, `x ↦ i₀`.  This uses (P1).
* Otherwise inject `K` into the indices `Fin (k-1)`: `a_q, b_q ↦ q`, and the
  core vertex and `x₀, x_*, y_*` to free indices, chosen by cases (II.2, II.3).
  `slotR_injOn` lists what has to be checked.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

section

variable (data : Certificates.PlusCaseAData G k s)

theorem c_adj_i0 (hP1 : P1 data) {p : Fin (k - 1)} (hp : p ≠ c2Index data) :
    G.Adj (data.cert.c p) (data.cert.i (i0Index data)) := by
  by_contra h
  have hP : p ∈ P data := (SecondConnector.TypeA.mem_P data p).2 h
  rw [show P data = {c2Index data} from hP1, Finset.mem_singleton] at hP
  exact hp hP

/-- The index `3` of the red certificate. -/
def c3Index : Fin (k - 1) := ⟨3, by have := data.cert.five_le_k; omega⟩

/-! ## II.1: projection -/

/-- core `g ↦ g`, `b_q ↦ c_q`, everything else `↦ i₀`. -/
noncomputable def projRed : SecondConnector.Vertex V k s → V
  | .inl (.inl (.core (.core v))) => v
  | .inl (.inl (.core (.b q))) => data.cert.c q
  | _ => data.cert.i (i0Index data)

@[simp] theorem projRed_core (v : V) : projRed data (core v) = v := rfl
@[simp] theorem projRed_b (q : Fin (k - 1)) : projRed data (b q) = data.cert.c q := rfl
@[simp] theorem projRed_x (r : Option (Fin (s - 1))) :
    projRed data (x data.cert r) = data.cert.i (i0Index data) := rfl

theorem pR_core_core {g g' : V} (hr : (oldGraph data).Adj (core g) (core g')) : G.Adj g g' := by
  simpa using hr

theorem pR_core_b {g : V} {q : Fin (k - 1)} (hr : (oldGraph data).Adj (core g) (b q)) :
    G.Adj g (data.cert.c q) := by
  rw [old_adj_core_b] at hr
  exact hr.2.symm

theorem pR_core_i0 (hP1 : P1 data) {g : V}
    (hg : (∃ p, g = data.cert.c p) ∨ g = data.cert.i (i0Index data) ∨
      G.Adj (data.cert.i (i0Index data)) g)
    (hgi : g ≠ data.cert.i (i0Index data)) (hgc : g ≠ data.cert.c (c2Index data)) :
    G.Adj g (data.cert.i (i0Index data)) := by
  rcases hg with ⟨p, rfl⟩ | h | h
  · exact c_adj_i0 data hP1 (fun hp ↦ hgc (by rw [hp]))
  · exact absurd h hgi
  · exact h.symm

theorem pR_core_x0 (hP1 : P1 data) {g : V}
    (hg : (∃ p, g = data.cert.c p) ∨ g = data.cert.i (i0Index data) ∨
      G.Adj (data.cert.i (i0Index data)) g)
    (hr : (oldGraph data).Adj (core g) (x data.cert (some (i0Index data)))) :
    G.Adj g (data.cert.i (i0Index data)) := by
  rw [old_adj_core_x_some] at hr
  exact pR_core_i0 data hP1 hg (fun h ↦ hr.1 h.symm) (fun h ↦ hr.2 h rfl)

theorem pR_core_xs (hP1 : P1 data) {g : V}
    (hg : (∃ p, g = data.cert.c p) ∨ g = data.cert.i (i0Index data) ∨
      G.Adj (data.cert.i (i0Index data)) g)
    (hr : (oldGraph data).Adj (core g) (x data.cert none)) :
    G.Adj g (data.cert.i (i0Index data)) := by
  rw [old_adj_core_x_none] at hr
  exact pR_core_i0 data hP1 hg hr.2
    (hr.1 _ (by rw [show P data = {c2Index data} from hP1]; simp))

theorem pR_core_x (hP1 : P1 data) {g : V}
    (hg : (∃ p, g = data.cert.c p) ∨ g = data.cert.i (i0Index data) ∨
      G.Adj (data.cert.i (i0Index data)) g)
    {r : Option (Fin (s - 1))} (hr' : r = none ∨ r = some (i0Index data))
    (hr : (oldGraph data).Adj (core g) (x data.cert r)) :
    G.Adj g (data.cert.i (i0Index data)) := by
  rcases hr' with rfl | rfl
  · exact pR_core_xs data hP1 hg hr
  · exact pR_core_x0 data hP1 hg hr

theorem pR_b_b {q q' : Fin (k - 1)} (h : (b q : SecondConnector.Vertex V k s) ≠ b q') :
    G.Adj (data.cert.c q) (data.cert.c q') :=
  data.cert.c_adj (fun hq ↦ h (by rw [hq]))

theorem nR_x0_xs (hr : (oldGraph data).Adj (x data.cert (some (i0Index data))) (x data.cert none)) :
    False :=
  old_not_adj_x_x data _ _ hr

/-! ## II.2, II.3: slots -/

/-- `a_q, b_q ↦ q`; core vertices `↦ σc`, `x₀ ↦ σ0`, `x_* ↦ σs`, `y_* ↦ σy`. -/
noncomputable def slotR (σc σ0 σs σy : Fin (k - 1)) : SecondConnector.Vertex V k s → Fin (k - 1)
  | .inl (.inl (.core (.core _))) => σc
  | .inl (.inl (.core (.a q))) => q
  | .inl (.inl (.core (.b q))) => q
  | .inl (.inl (.a r)) =>
      match Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r with
      | none => σs
      | some _ => σ0
  | _ => σy

variable {σc σ0 σs σy : Fin (k - 1)}

@[simp] theorem slotR_core (v : V) : slotR data σc σ0 σs σy (core v) = σc := rfl
@[simp] theorem slotR_a (q : Fin (k - 1)) : slotR data σc σ0 σs σy (a q) = q := rfl
@[simp] theorem slotR_b (q : Fin (k - 1)) : slotR data σc σ0 σs σy (b q) = q := rfl
@[simp] theorem slotR_x0 (q : Fin (s - 1)) : slotR data σc σ0 σs σy (x data.cert (some q)) = σ0 := by
  simp [slotR]
@[simp] theorem slotR_xs : slotR data σc σ0 σs σy (x data.cert none) = σs := by
  simp [slotR]
@[simp] theorem slotR_ys : slotR data σc σ0 σs σy (y data.cert none) = σy := rfl

/-- What has to be checked for `slotR` to be injective on a red clique in the
red neighborhood of `u`. -/
theorem slotR_injOn {t : Finset (SecondConnector.Vertex V k s)}
    (hsub : ↑t ⊆ {v | redToU data v})
    (hred : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data).Adj u v)
    (hc0 : ∀ g g', core g ∈ t → core g' ∈ t → g = g')
    (hca : ∀ g q, core g ∈ t → a q ∈ t → σc ≠ q)
    (hcb : ∀ g q, core g ∈ t → b q ∈ t → σc ≠ q)
    (hcx : ∀ g, core g ∈ t → x data.cert (some (i0Index data)) ∈ t → σc ≠ σ0)
    (hcs : ∀ g, core g ∈ t → x data.cert none ∈ t → σc ≠ σs)
    (hcy : ∀ g, core g ∈ t → y data.cert none ∈ t → σc ≠ σy)
    (hax : ∀ q, a q ∈ t → x data.cert (some (i0Index data)) ∈ t → q ≠ σ0)
    (has : ∀ q, a q ∈ t → x data.cert none ∈ t → q ≠ σs)
    (hay : ∀ q, a q ∈ t → y data.cert none ∈ t → q ≠ σy)
    (hbx : ∀ q, b q ∈ t → x data.cert (some (i0Index data)) ∈ t → q ≠ σ0)
    (hbs : ∀ q, b q ∈ t → x data.cert none ∈ t → q ≠ σs)
    (hby : ∀ q, b q ∈ t → y data.cert none ∈ t → q ≠ σy)
    (hsy : x data.cert none ∈ t → y data.cert none ∈ t → σs ≠ σy) :
    Set.InjOn (slotR data σc σ0 σs σy) t := by
  intro u₁ hu₁ u₂ hu₂ heq
  by_contra hne
  have hr := hred _ hu₁ _ hu₂ hne
  rcases mem_redU data (hsub hu₁) with ⟨g₁, -, rfl⟩ | ⟨q₁, -, rfl⟩ | ⟨q₁, -, rfl⟩ | rfl | rfl |
      rfl <;>
    rcases mem_redU data (hsub hu₂) with ⟨g₂, -, rfl⟩ | ⟨q₂, -, rfl⟩ | ⟨q₂, -, rfl⟩ | rfl | rfl |
      rfl <;>
    (try simp only [slotR_core, slotR_a, slotR_b, slotR_x0, slotR_xs, slotR_ys] at heq) <;>
    first
    | exact hne rfl
    | exact hne (by rw [hc0 g₁ g₂ hu₁ hu₂])
    | exact hca g₁ q₂ hu₁ hu₂ heq
    | exact hca g₂ q₁ hu₂ hu₁ heq.symm
    | exact hcb g₁ q₂ hu₁ hu₂ heq
    | exact hcb g₂ q₁ hu₂ hu₁ heq.symm
    | exact hcx g₁ hu₁ hu₂ heq
    | exact hcx g₂ hu₂ hu₁ heq.symm
    | exact hcs g₁ hu₁ hu₂ heq
    | exact hcs g₂ hu₂ hu₁ heq.symm
    | exact hcy g₁ hu₁ hu₂ heq
    | exact hcy g₂ hu₂ hu₁ heq.symm
    | exact hax q₁ hu₁ hu₂ heq
    | exact hax q₂ hu₂ hu₁ heq.symm
    | exact has q₁ hu₁ hu₂ heq
    | exact has q₂ hu₂ hu₁ heq.symm
    | exact hay q₁ hu₁ hu₂ heq
    | exact hay q₂ hu₂ hu₁ heq.symm
    | exact hbx q₁ hu₁ hu₂ heq
    | exact hbx q₂ hu₂ hu₁ heq.symm
    | exact hbs q₁ hu₁ hu₂ heq
    | exact hbs q₂ hu₂ hu₁ heq.symm
    | exact hby q₁ hu₁ hu₂ heq
    | exact hby q₂ hu₂ hu₁ heq.symm
    | exact hsy hu₁ hu₂ heq
    | exact hsy hu₂ hu₁ heq.symm
    | (subst heq; exact hne rfl)
    | (subst heq; simp at hr)

/-! ## Part II -/

/-- Part II: no red `K_k` in the red neighborhood of `u`. -/
theorem redU_cliqueFree (hP1 : P1 data) (hG : IsRamseyFree G k s) :
    (oldGraph data).CliqueFreeOn {v | redToU data v} k := by
  classical
  intro t hsub ht
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  have hk := data.cert.five_le_k
  have hmemR : ∀ u ∈ t, _ := fun u hu ↦ mem_redU data (hsub hu)
  have hred : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data).Adj u v :=
    fun u hu v hv huv ↦ ht.isClique hu hv huv
  have v0 : (c0Index data).val = 0 := rfl
  have v1 : (c1Index data).val = 1 := rfl
  have v2 : (c2Index data).val = 2 := rfl
  have v3 : (c3Index data).val = 3 := rfl
  have haEven : ∀ q, a q ∈ t → q.val % 2 = 0 := fun q hq ↦ (redToU_a data q).1 (hsub hq)
  have hbNe2 : ∀ q, b q ∈ t → q ≠ c2Index data := fun q hq ↦ (redToU_b data q).1 (hsub hq)
  have hcoreYs : ∀ g, core g ∈ t → y data.cert none ∈ t → g = data.cert.c (c0Index data) :=
    fun g hg hy ↦ ((old_adj_core_y_none data g).1 (hred _ hg _ hy (by simp))).symm
  have hcoreX0 : ∀ g, core g ∈ t → x data.cert (some (i0Index data)) ∈ t →
      g ≠ data.cert.c (c2Index data) ∧ g ≠ data.cert.i (i0Index data) := by
    intro g hg hx
    have := hred _ hg _ hx (by simp)
    rw [old_adj_core_x_some] at this
    exact ⟨fun h ↦ this.2 h rfl, fun h ↦ this.1 h.symm⟩
  have hcoreXs : ∀ g, core g ∈ t → x data.cert none ∈ t →
      g ≠ data.cert.c (c2Index data) ∧ g ≠ data.cert.i (i0Index data) := by
    intro g hg hx
    have := hred _ hg _ hx (by simp)
    rw [old_adj_core_x_none] at this
    exact ⟨this.1 _ (by rw [show P data = {c2Index data} from hP1]; simp), this.2⟩
  have hx0xs : x data.cert (some (i0Index data)) ∈ t → x data.cert none ∈ t → False :=
    fun h0 hs ↦ nR_x0_xs data (hred _ h0 _ hs (by simp))
  have hx0ys : x data.cert (some (i0Index data)) ∈ t → y data.cert none ∈ t → False := by
    intro h0 hy
    have := hred _ h0 _ hy (by simp)
    simp at this
  have hbXs : ∀ q, b q ∈ t → x data.cert none ∈ t → q ≠ c0Index data := by
    intro q hq hx hq0
    subst hq0
    have := hred _ hq _ hx (by simp)
    rw [old_adj_b_x] at this
    exact this ⟨rfl, Or.inr rfl⟩
  have hbCore : ∀ q, b q ∈ t → core (data.cert.c q) ∈ t → False := by
    intro q hq hc
    have := hred _ hq _ hc (by simp)
    simp at this
  -- the `b` of a red clique lie in one block
  have hbBlock : ∀ q q', b q ∈ t → b q' ∈ t → q.val < 2 → 2 ≤ q'.val → False := by
    intro q q' hq hq' hlt hge
    have hne : (b q : SecondConnector.Vertex V k s) ≠ b q' := fun h ↦ by
      have := congrArg Fin.val (SecondConnector.vertex_b_injective (Sum.inl.inj h))
      omega
    have := hred _ hq _ hq' hne
    rw [old_adj_b_b] at this
    rcases this with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · simp only [SameBPart] at h
      omega
    · exact hbNe2 q' hq' h
    · have := congrArg Fin.val h
      omega
  have hcard : ∀ σc σ0 σs σy, Set.InjOn (slotR data σc σ0 σs σy) t → False := by
    intro σc σ0 σs σy hinj
    have := card_le_of_slot (slotR data σc σ0 σs σy) hinj
    rw [ht.card_eq] at this
    omega
  by_cases ha : ∃ p, a p ∈ t
  · -- II.2: some `a_p`
    obtain ⟨p₀, hp₀⟩ := ha
    have hcoreA : ∀ g q, core g ∈ t → a q ∈ t →
        data.cert.c q = g ∨ (q = c2Index data ∧ g = data.cert.i (i0Index data)) :=
      fun g q hg hq ↦ (old_adj_core_a data g q).1 (hred _ hg _ hq (by simp))
    have hc0 : ∀ g g', core g ∈ t → core g' ∈ t → g = g' := by
      intro g g' hg hg'
      by_contra hne
      have h3 := hred _ hg _ hg' (by simpa using hne)
      rw [old_adj_core_core] at h3
      rcases hcoreA g p₀ hg hp₀ with h1 | ⟨hp2, h1⟩ <;>
        rcases hcoreA g' p₀ hg' hp₀ with h2 | ⟨hp2', h2⟩
      · exact hne (h1.symm.trans h2)
      · rw [← h1, h2, hp2'] at h3
        exact data.c2_i0_blue h3
      · rw [h1, ← h2, hp2] at h3
        exact data.c2_i0_blue h3.symm
      · exact hne (h1.trans h2.symm)
    have haXs : ∀ q, a q ∈ t → x data.cert none ∈ t → q ≠ c0Index data := by
      intro q hq hx hq0
      subst hq0
      have := hred _ hq _ hx (by simp)
      rw [old_adj_a_x data hE] at this
      exact this ⟨rfl, rfl⟩
    -- a core vertex together with `a₂` is `c₂` or `i₀`, so it is blue to `x₀`, `x_*`, `y_*`
    have hcoreA2 : ∀ g, core g ∈ t → a (c2Index data) ∈ t →
        x data.cert (some (i0Index data)) ∈ t ∨ x data.cert none ∈ t ∨ y data.cert none ∈ t →
        False := by
      intro g hg ha2 hE'
      have hg2 : g = data.cert.c (c2Index data) ∨ g = data.cert.i (i0Index data) := by
        rcases hcoreA g _ hg ha2 with h | ⟨-, h⟩
        · exact Or.inl h.symm
        · exact Or.inr h
      rcases hE' with hx | hx | hy
      · rcases hg2 with h | h
        · exact (hcoreX0 g hg hx).1 h
        · exact (hcoreX0 g hg hx).2 h
      · rcases hg2 with h | h
        · exact (hcoreXs g hg hx).1 h
        · exact (hcoreXs g hg hx).2 h
      · have := hcoreYs g hg hy
        rcases hg2 with h | h
        · rw [h] at this
          exact c0_ne_c2 data (data.cert.c.injective this).symm
        · rw [h] at this
          exact data.cert.c_ne_i _ _ this.symm
    have hodd : ∀ q, a q ∈ t → ∀ c : Fin (k - 1), c.val % 2 = 1 → q ≠ c := by
      intro q hq c hc h
      have := haEven q hq
      rw [h] at this
      omega
    by_cases hlow : ∃ q, b q ∈ t ∧ q.val < 2
    · -- the `b` are in `{b₀, b₁}`: `x₀, y_* ↦ 3`, `x_* ↦ 0`, the core vertex `↦ 2` or `3`
      obtain ⟨qL, hqL, hqLv⟩ := hlow
      have hbLow : ∀ q, b q ∈ t → q.val < 2 := fun q hq ↦ by
        by_contra h
        exact hbBlock qL q hqL hq hqLv (by omega)
      let E : Prop := x data.cert (some (i0Index data)) ∈ t ∨ x data.cert none ∈ t ∨
        y data.cert none ∈ t
      refine hcard (if E then c2Index data else c3Index data) (c3Index data) (c0Index data)
        (c3Index data) (slotR_injOn data hsub hred hc0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · intro g q hg hq h
        split_ifs at h with hE'
        · rw [← h] at hq
          exact hcoreA2 g hg hq hE'
        · exact hodd q hq _ (by rw [v3]) h.symm
      · intro g q _ hq h
        have := hbLow q hq
        split_ifs at h <;> (have := congrArg Fin.val h; omega)
      · intro g _ hx h
        rw [if_pos (Or.inl hx)] at h
        have := congrArg Fin.val h
        omega
      · intro g _ _ h
        split_ifs at h <;> (have := congrArg Fin.val h; omega)
      · intro g _ hy h
        rw [if_pos (Or.inr (Or.inr hy))] at h
        have := congrArg Fin.val h
        omega
      · intro q hq _
        exact hodd q hq _ (by rw [v3])
      · intro q hq hx
        exact haXs q hq hx
      · intro q hq _
        exact hodd q hq _ (by rw [v3])
      · intro q hq _ h
        have := hbLow q hq
        have := congrArg Fin.val h
        omega
      · intro q hq hx
        exact hbXs q hq hx
      · intro q hq _ h
        have := hbLow q hq
        have := congrArg Fin.val h
        omega
      · intro _ _ h
        have := congrArg Fin.val h
        omega
    · -- the `b` are in `{b₃, …}`
      have hbHigh : ∀ q, b q ∈ t → 3 ≤ q.val := fun q hq ↦ by
        have h2 : 2 ≤ q.val := by
          by_contra h
          exact hlow ⟨q, hq, by omega⟩
        have := hbNe2 q hq
        by_contra h3
        exact this (Fin.ext (by omega))
      let xs : Prop := x data.cert none ∈ t
      let E : Prop := x data.cert (some (i0Index data)) ∈ t ∨ y data.cert none ∈ t
      refine hcard (if xs then c0Index data else if E then c2Index data else c1Index data)
        (c1Index data) (c1Index data) (if xs then c0Index data else c1Index data)
        (slotR_injOn data hsub hred hc0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      · intro g q hg hq h
        split_ifs at h with hxs hE'
        · rw [← h] at hq
          exact haXs _ hq hxs rfl
        · rw [← h] at hq
          rcases hE' with hx | hy
          · exact hcoreA2 g hg hq (Or.inl hx)
          · exact hcoreA2 g hg hq (Or.inr (Or.inr hy))
        · exact hodd q hq _ (by rw [v1]) h.symm
      · intro g q _ hq h
        have := hbHigh q hq
        split_ifs at h <;> (have := congrArg Fin.val h; omega)
      · intro g _ hx h
        split_ifs at h with hxs hE'
        · exact hx0xs hx hxs
        · have := congrArg Fin.val h
          omega
        · exact hE' (Or.inl hx)
      · intro g _ hxs h
        rw [if_pos hxs] at h
        have := congrArg Fin.val h
        omega
      · intro g hg hy h
        by_cases hxs : x data.cert none ∈ t
        · -- the core vertex is `c₀`, red to `a_p` only for `p = 0`, but `a₀` is blue to `x_*`
          have hg0 := hcoreYs g hg hy
          rcases hcoreA g p₀ hg hp₀ with h1 | ⟨-, h1⟩
          · rw [hg0] at h1
            exact haXs p₀ hp₀ hxs (data.cert.c.injective h1)
          · rw [hg0] at h1
            exact data.cert.c_ne_i _ _ h1
        · rw [if_neg hxs, if_neg hxs, if_pos (Or.inr hy)] at h
          have := congrArg Fin.val h
          omega
      · intro q hq _
        exact hodd q hq _ (by rw [v1])
      · intro q hq _
        exact hodd q hq _ (by rw [v1])
      · intro q hq _
        split_ifs with hxs
        · exact haXs q hq hxs
        · exact hodd q hq _ (by rw [v1])
      · intro q hq _ h
        have := hbHigh q hq
        have := congrArg Fin.val h
        omega
      · intro q hq _ h
        have := hbHigh q hq
        have := congrArg Fin.val h
        omega
      · intro q hq _ h
        have := hbHigh q hq
        split_ifs at h <;> (have := congrArg Fin.val h; omega)
      · intro hxs _ h
        rw [if_pos hxs] at h
        have := congrArg Fin.val h
        omega
  · by_cases hys : y data.cert none ∈ t
    · -- II.3: no `a`, `y_* ∈ K`; the core vertex is `c₀` and `x₀ ∉ K`
      have hc0 : ∀ g g', core g ∈ t → core g' ∈ t → g = g' := fun g g' hg hg' ↦
        (hcoreYs g hg hys).trans (hcoreYs g' hg' hys).symm
      have hna : ∀ q, a q ∈ t → False := fun q hq ↦ ha ⟨q, hq⟩
      have hcb0 : ∀ g q, core g ∈ t → b q ∈ t → c0Index data ≠ q := by
        intro g q hg hq h
        rw [← h] at hq
        rw [hcoreYs g hg hys] at hg
        exact hbCore _ hq hg
      by_cases hlow : ∃ q, b q ∈ t ∧ q.val < 2
      · obtain ⟨qL, hqL, hqLv⟩ := hlow
        have hbLow : ∀ q, b q ∈ t → q.val < 2 := fun q hq ↦ by
          by_contra h
          exact hbBlock qL q hqL hq hqLv (by omega)
        refine hcard (c0Index data) (c0Index data) (c2Index data) (c3Index data)
          (slotR_injOn data hsub hred hc0 (fun _ q _ hq ↦ (hna q hq).elim) hcb0
            (fun _ _ hx ↦ (hx0ys hx hys).elim) ?_ ?_ (fun q hq ↦ (hna q hq).elim)
            (fun q hq ↦ (hna q hq).elim) (fun q hq ↦ (hna q hq).elim)
            (fun _ _ hx ↦ (hx0ys hx hys).elim) ?_ ?_ ?_)
        · intro _ _ _ h
          have := congrArg Fin.val h
          omega
        · intro _ _ _ h
          have := congrArg Fin.val h
          omega
        · intro q hq _
          exact hbNe2 q hq
        · intro q hq _ h
          have := hbLow q hq
          have := congrArg Fin.val h
          omega
        · intro _ _ h
          have := congrArg Fin.val h
          omega
      · have hbHigh : ∀ q, b q ∈ t → 3 ≤ q.val := fun q hq ↦ by
          have h2 : 2 ≤ q.val := by
            by_contra h
            exact hlow ⟨q, hq, by omega⟩
          have := hbNe2 q hq
          by_contra h3
          exact this (Fin.ext (by omega))
        refine hcard (c0Index data) (c0Index data) (c1Index data) (c2Index data)
          (slotR_injOn data hsub hred hc0 (fun _ q _ hq ↦ (hna q hq).elim) hcb0
            (fun _ _ hx ↦ (hx0ys hx hys).elim) ?_ ?_ (fun q hq ↦ (hna q hq).elim)
            (fun q hq ↦ (hna q hq).elim) (fun q hq ↦ (hna q hq).elim)
            (fun _ _ hx ↦ (hx0ys hx hys).elim) ?_ ?_ ?_)
        · intro _ _ _ h
          have := congrArg Fin.val h
          omega
        · intro _ _ _ h
          have := congrArg Fin.val h
          omega
        · intro q hq _ h
          have := hbHigh q hq
          have := congrArg Fin.val h
          omega
        · intro q hq _
          exact hbNe2 q hq
        · intro _ _ h
          have := congrArg Fin.val h
          omega
    · -- II.1: no `a`, no `y_*`: project to a red clique of `G`
      have hmem' : ∀ u ∈ t,
          (∃ g, ((∃ p, g = data.cert.c p) ∨ g = data.cert.i (i0Index data) ∨
            G.Adj (data.cert.i (i0Index data)) g) ∧ u = core g) ∨
          (∃ q, q ≠ c2Index data ∧ u = b q) ∨ u = x data.cert none ∨
          u = x data.cert (some (i0Index data)) := by
        intro u hu
        rcases hmemR u hu with h | ⟨p, -, rfl⟩ | h | h | h | rfl
        · exact Or.inl h
        · exact (ha ⟨p, hu⟩).elim
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact (hys hu).elim
      refine false_of_projection hG.1 ht (projRed data) ?_
      intro u hu v hv huv
      have hr := hred u hu v hv huv
      rcases hmem' u hu with ⟨g, hg, rfl⟩ | ⟨q, hq, rfl⟩ | rfl | rfl <;>
        rcases hmem' v hv with ⟨g', hg', rfl⟩ | ⟨q', hq', rfl⟩ | rfl | rfl <;>
        simp only [projRed_core, projRed_b, projRed_x]
      · exact pR_core_core data hr
      · exact pR_core_b data hr
      · exact pR_core_xs data hP1 hg hr
      · exact pR_core_x0 data hP1 hg hr
      · exact (pR_core_b data hr.symm).symm
      · exact pR_b_b data huv
      · exact c_adj_i0 data hP1 hq
      · exact c_adj_i0 data hP1 hq
      · exact (pR_core_xs data hP1 hg' hr.symm).symm
      · exact (c_adj_i0 data hP1 hq').symm
      · exact (huv rfl).elim
      · exact absurd hr (old_not_adj_x_x data _ _)
      · exact (pR_core_x0 data hP1 hg' hr.symm).symm
      · exact (c_adj_i0 data hP1 hq').symm
      · exact absurd hr (old_not_adj_x_x data _ _)
      · exact (huv rfl).elim
end

end ThirdConnector
end RamseyIncrement
