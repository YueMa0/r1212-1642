/-
Rule R*, Part III: no blue `K_s` in the blue neighborhood of `u`.
-/
import RamseyIncrement.ThirdConnector.Projection

/-!
# Part III: blue cliques through `u`

Let `K` be a blue clique in the blue neighborhood of `u`.

* If `K` has no `x`, project it to a blue clique of `G`:
  core `g ↦ g`, `y_q ↦ i_q`, `a_p ↦ i₀`, `b₂ ↦ c₂`, `w ↦ i₀`, and
  `z ↦ i₀` when `b₂ ∈ K`, `z ↦ c₀` otherwise.  This is III.1 and III.3.
* If `K` has some `x_r` (III.2), then `K` has no `a` and no `b₂`, and every core
  vertex of `K` is `i_r`.  Without core vertices, `x_q, y_q ↦ q`, `z, w ↦ 0`
  injects `K` into `Fin (s-1)`.  With the core vertex `i_r`, either `K` has a
  `y` of index `0` or `1` and at most four vertices, or a free slot for `i_r`
  is found.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

section

variable (data : Certificates.PlusCaseAData G k s)

/-! ## Colours used below -/

theorem i0_mem_T : i0Index data ∈ data.cert.T := by
  rw [Certificates.OrderedCertificates.mem_T]
  exact data.c0_i0_red

theorem y0_z_red : (oldGraph data).Adj (y data.cert (some (i0Index data))) z :=
  (old_adj_y_z data _).2 ⟨_, i0_mem_T data, rfl⟩

theorem y0_w_red : (oldGraph data).Adj (y data.cert (some (i0Index data))) w := by
  simp [y]

theorem y2_w_red : (oldGraph data).Adj (y data.cert (some (i2Index data))) w := by
  simp [y]

theorem x1_z_red : (oldGraph data).Adj (x data.cert (some (Switching.Vertex.i1 data.cert))) z :=
  (old_adj_x_z data _).2 (Or.inl rfl)

theorem a_x_red (hE : data.cert.E = ∅) (p : Fin (k - 1)) (q : Fin (s - 1)) :
    (oldGraph data).Adj (a p) (x data.cert (some q)) :=
  (old_adj_a_x data hE p _).2 (by simp)

theorem b_x_red (p : Fin (k - 1)) (hp : p ≠ c0Index data) (q : Fin (s - 1)) :
    (oldGraph data).Adj (b p) (x data.cert (some q)) :=
  (old_adj_b_x data p _).2 (fun h ↦ hp h.1)

theorem q_cases (q : Fin (s - 1)) :
    q = i0Index data ∨ q = Switching.Vertex.i1 data.cert ∨ q = i2Index data ∨ 3 ≤ q.val := by
  have v0 : (i0Index data).val = 0 := rfl
  have v1 : (Switching.Vertex.i1 data.cert).val = 1 := rfl
  have v2 : (i2Index data).val = 2 := rfl
  rcases Nat.lt_or_ge q.val 3 with h | h
  · interval_cases hq : q.val
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext (by omega))))
  · exact Or.inr (Or.inr (Or.inr h))

/-- `y₀` is red to `y_q` for `q ≥ 3`. -/
theorem y0_red_high (hE : data.cert.E = ∅) {q : Fin (s - 1)} (hq : 3 ≤ q.val) :
    (oldGraph data).Adj (y data.cert (some (i0Index data))) (y data.cert (some q)) := by
  have v0 : (i0Index data).val = 0 := rfl
  have v2 : (i2Index data).val = 2 := rfl
  rw [old_adj_y_y data hE]
  refine ⟨fun h ↦ ?_, ?_, ?_, ?_⟩
  · have := congrArg Fin.val (Option.some.inj h)
    omega
  · simp only [YLow, v0]
    omega
  · simp [Switching.SymmPair]
  · simp only [Switching.SymmPair, Option.some.injEq, not_or, not_and]
    refine ⟨fun _ h ↦ ?_, fun h ↦ ?_⟩
    · have := congrArg Fin.val h
      omega
    · have := congrArg Fin.val h
      omega

/-- `y₁` is red to `y_q` for `q ≥ 2`. -/
theorem y1_red_high (hE : data.cert.E = ∅) {q : Fin (s - 1)} (hq : 2 ≤ q.val) :
    (oldGraph data).Adj (y data.cert (some (Switching.Vertex.i1 data.cert)))
      (y data.cert (some q)) := by
  have v0 : (i0Index data).val = 0 := rfl
  have v1 : (Switching.Vertex.i1 data.cert).val = 1 := rfl
  have v2 : (i2Index data).val = 2 := rfl
  rw [old_adj_y_y data hE]
  refine ⟨fun h ↦ ?_, ?_, ?_, ?_⟩
  · have := congrArg Fin.val (Option.some.inj h)
    omega
  · simp only [YLow, v1]
    omega
  · simp only [Switching.SymmPair]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · have := congrArg Fin.val (Option.some.inj h1)
      omega
    · simp at h1
  · simp only [Switching.SymmPair, Option.some.injEq, not_or, not_and]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have := congrArg Fin.val h
      omega
    · have := congrArg Fin.val h
      omega

/-! ## The projection for blue cliques without `x` -/

/-- `core g ↦ g`, `y_q ↦ i_q`, `b ↦ c₂`, `z ↦ i₀` or `c₀`, everything else `↦ i₀`. -/
noncomputable def projBlue (bt : Prop) [Decidable bt] : SecondConnector.Vertex V k s → V
  | .inl (.inl (.core (.core v))) => v
  | .inl (.inl (.core (.b _))) => data.cert.c (c2Index data)
  | .inl (.inl (.b r)) =>
      match Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r with
      | some q => data.cert.i q
      | none => data.cert.i (i0Index data)
  | .inl (.inr _) => if bt then data.cert.i (i0Index data) else data.cert.c (c0Index data)
  | _ => data.cert.i (i0Index data)

variable {bt : Prop} [Decidable bt]

@[simp] theorem projBlue_core (v : V) : projBlue data bt (core v) = v := rfl
@[simp] theorem projBlue_a (p : Fin (k - 1)) :
    projBlue data bt (a p) = data.cert.i (i0Index data) := rfl
@[simp] theorem projBlue_b (p : Fin (k - 1)) :
    projBlue data bt (b p) = data.cert.c (c2Index data) := rfl
@[simp] theorem projBlue_y (q : Fin (s - 1)) :
    projBlue data bt (y data.cert (some q)) = data.cert.i q := by
  simp [projBlue]
@[simp] theorem projBlue_w : projBlue data bt w = data.cert.i (i0Index data) := rfl
theorem projBlue_z :
    projBlue data bt z = if bt then data.cert.i (i0Index data) else data.cert.c (c0Index data) :=
  rfl

theorem pB_core_core {g g' : V} (hb : (oldGraph data)ᶜ.Adj (core g) (core g')) :
    Gᶜ.Adj g g' := by
  rw [SimpleGraph.compl_adj] at hb ⊢
  simpa using hb

theorem pB_core_i0 {g : V} (hgi : g ≠ data.cert.i (i0Index data))
    (hgG : ¬G.Adj (data.cert.i (i0Index data)) g) : Gᶜ.Adj g (data.cert.i (i0Index data)) :=
  (SimpleGraph.compl_adj _ _ _).2 ⟨hgi, fun h ↦ hgG h.symm⟩

theorem pB_core_b2 {g : V} (hgC : ∀ p, g ≠ data.cert.c p)
    (hb : (oldGraph data)ᶜ.Adj (core g) (b (c2Index data))) :
    Gᶜ.Adj g (data.cert.c (c2Index data)) := by
  rw [SimpleGraph.compl_adj] at hb ⊢
  refine ⟨hgC _, fun h ↦ hb.2 ?_⟩
  rw [old_adj_core_b]
  exact ⟨hgC _, h.symm⟩

theorem pB_core_y {g : V} {q : Fin (s - 1)}
    (hb : (oldGraph data)ᶜ.Adj (core g) (y data.cert (some q))) : Gᶜ.Adj g (data.cert.i q) := by
  rw [SimpleGraph.compl_adj, old_adj_core_y_some, not_or] at hb
  exact (SimpleGraph.compl_adj _ _ _).2 ⟨hb.2.1, fun h ↦ hb.2.2 h.symm⟩

theorem pB_core_z {g : V} (hgC : ∀ p, g ≠ data.cert.c p) (hgi : g ≠ data.cert.i (i0Index data))
    (hgG : ¬G.Adj (data.cert.i (i0Index data)) g) (hb : (oldGraph data)ᶜ.Adj (core g) z) :
    Gᶜ.Adj g (projBlue data bt z) := by
  rw [projBlue_z]
  split_ifs
  · exact pB_core_i0 data hgi hgG
  · rw [SimpleGraph.compl_adj] at hb ⊢
    refine ⟨hgC _, fun h ↦ hb.2 ?_⟩
    rw [old_adj_core_z]
    exact ⟨hgC _, h.symm⟩

theorem pB_a_y {p : Fin (k - 1)} {q : Fin (s - 1)} (hp : p.val % 2 = 1)
    (hb : (oldGraph data)ᶜ.Adj (a p) (y data.cert (some q))) :
    Gᶜ.Adj (data.cert.i (i0Index data)) (data.cert.i q) := by
  apply data.cert.i_compl_adj
  rintro rfl
  rw [SimpleGraph.compl_adj] at hb
  exact hb.2 ((old_adj_a_y_some data p _).2 (Or.inr ⟨hp, rfl⟩))

theorem pB_b2_y {q : Fin (s - 1)}
    (hb : (oldGraph data)ᶜ.Adj (b (c2Index data)) (y data.cert (some q))) :
    Gᶜ.Adj (data.cert.c (c2Index data)) (data.cert.i q) := by
  rw [SimpleGraph.compl_adj] at hb ⊢
  refine ⟨data.cert.c_ne_i _ _, fun h ↦ hb.2 ?_⟩
  rw [old_adj_b_y_some]
  exact ⟨(c0_ne_c2 data).symm, h⟩

theorem pB_b2_i0 : Gᶜ.Adj (data.cert.c (c2Index data)) (data.cert.i (i0Index data)) :=
  (SimpleGraph.compl_adj _ _ _).2 ⟨data.cert.c_ne_i _ _, data.c2_i0_blue⟩

theorem pB_y_y {q q' : Fin (s - 1)} (h : y data.cert (some q) ≠ y data.cert (some q')) :
    Gᶜ.Adj (data.cert.i q) (data.cert.i q') :=
  data.cert.i_compl_adj (fun hq ↦ h (by rw [hq]))

theorem pB_y_z {q : Fin (s - 1)} (hb : (oldGraph data)ᶜ.Adj (y data.cert (some q)) z) :
    Gᶜ.Adj (data.cert.i q) (projBlue data bt z) := by
  rw [SimpleGraph.compl_adj, old_adj_y_z] at hb
  have hqT : q ∉ data.cert.T := fun h ↦ hb.2 ⟨q, h, rfl⟩
  rw [projBlue_z]
  split_ifs
  · apply data.cert.i_compl_adj
    rintro rfl
    exact hqT (i0_mem_T data)
  · rw [SimpleGraph.compl_adj]
    refine ⟨fun h ↦ data.cert.c_ne_i _ _ h.symm, fun h ↦ hqT ?_⟩
    rw [Certificates.OrderedCertificates.mem_T]
    exact h.symm

theorem pB_y_w {q : Fin (s - 1)} (hb : (oldGraph data)ᶜ.Adj (y data.cert (some q)) w) :
    Gᶜ.Adj (data.cert.i q) (data.cert.i (i0Index data)) := by
  apply data.cert.i_compl_adj
  rintro rfl
  rw [SimpleGraph.compl_adj] at hb
  exact hb.2 (y0_w_red data)

theorem nB_a_a {p p' : Fin (k - 1)} (hb : (oldGraph data)ᶜ.Adj (a p) (a p')) : False := by
  rw [SimpleGraph.compl_adj, old_adj_a_a] at hb
  exact hb.1 (by rw [not_not.1 hb.2])

theorem nB_a_b2 {p : Fin (k - 1)} (hp : p.val % 2 = 1)
    (hb : (oldGraph data)ᶜ.Adj (a p) (b (c2Index data))) : False := by
  rw [SimpleGraph.compl_adj, old_adj_a_b] at hb
  exact hb.2 (c_val_ne_of_odd data hp).2

theorem nB_a_z {p : Fin (k - 1)} (hp : p.val % 2 = 1) (hb : (oldGraph data)ᶜ.Adj (a p) z) :
    False := by
  rw [SimpleGraph.compl_adj, old_adj_a_z] at hb
  exact hb.2 (c_val_ne_of_odd data hp).1

theorem nB_a_w {p : Fin (k - 1)} (hp : p.val % 2 = 1) (hb : (oldGraph data)ᶜ.Adj (a p) w) :
    False := by
  rw [SimpleGraph.compl_adj] at hb
  exact hb.2 ((old_adj_old_w data _).2
    ((SecondConnector.TypeA.redToWA_a data p).2 (c_val_ne_of_odd data hp).2))

theorem nB_z_w (hb : (oldGraph data)ᶜ.Adj z w) : False := by
  rw [SimpleGraph.compl_adj] at hb
  exact hb.2 ((old_adj_old_w data _).2 (SecondConnector.TypeA.redToWA_z data))

/-! ## Slots for blue cliques with an `x` -/

/-- `x_q, y_q ↦ q`, core vertices `↦ σ`, everything else `↦ 0`. -/
noncomputable def slotXY (σ : Fin (s - 1)) : SecondConnector.Vertex V k s → Fin (s - 1)
  | .inl (.inl (.a r)) =>
      (Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r).getD
        (i0Index data)
  | .inl (.inl (.b r)) =>
      (Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r).getD
        (i0Index data)
  | .inl (.inl (.core (.core _))) => σ
  | _ => i0Index data

@[simp] theorem slotXY_x (σ q : Fin (s - 1)) : slotXY data σ (x data.cert (some q)) = q := by
  simp [slotXY]
@[simp] theorem slotXY_y (σ q : Fin (s - 1)) : slotXY data σ (y data.cert (some q)) = q := by
  simp [slotXY]
@[simp] theorem slotXY_core (σ : Fin (s - 1)) (v : V) : slotXY data σ (core v) = σ := rfl
@[simp] theorem slotXY_z (σ : Fin (s - 1)) : slotXY data σ z = i0Index data := rfl
@[simp] theorem slotXY_w (σ : Fin (s - 1)) : slotXY data σ w = i0Index data := rfl

@[simp] theorem slotXY_a (σ : Fin (s - 1)) (p : Fin (k - 1)) : slotXY data σ (a p) = i0Index data :=
  rfl
@[simp] theorem slotXY_b (σ : Fin (s - 1)) (p : Fin (k - 1)) : slotXY data σ (b p) = i0Index data :=
  rfl

theorem y_some_ne {q q' : Fin (s - 1)} (h : q ≠ q') :
    y data.cert (some q) ≠ y data.cert (some q') := fun e ↦
  h (Option.some.inj (SecondConnector.vertex_y_injective data.cert (Sum.inl.inj e)))

/-! ## Part III -/

/-- Part III: no blue `K_s` in the blue neighborhood of `u`. -/
theorem blueU_cliqueFree (hG : IsRamseyFree G k s) :
    (oldGraph data)ᶜ.CliqueFreeOn {v | ¬redToU data v} s := by
  classical
  intro t hsub ht
  have hE := data.cert.caseA_E_eq_empty hG data.caseA
  have hs := data.cert.five_le_s
  have hmem : ∀ u ∈ t, _ := fun u hu ↦ mem_blueU data (hsub hu)
  have hblue : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data)ᶜ.Adj u v :=
    fun u hu v hv huv ↦ ht.isClique hu hv huv
  have h01 := i0_ne_i1 data
  have v0 : (i0Index data).val = 0 := rfl
  have v1 : (Switching.Vertex.i1 data.cert).val = 1 := rfl
  have v2 : (i2Index data).val = 2 := rfl
  by_cases hx : ∃ q, x data.cert (some q) ∈ t
  · -- III.2: some `x_r` in the clique
    obtain ⟨r, hr⟩ := hx
    have hr0 : r ≠ i0Index data := by
      rintro rfl
      exact hsub hr ((redToU_x data _).2 (Or.inr rfl))
    have hna : ∀ p, a p ∈ t → False := fun p hp ↦
      ((SimpleGraph.compl_adj _ _ _).1 (hblue _ hp _ hr (by simp))).2 (a_x_red data hE p r)
    have hnb : b (c2Index data) ∈ t → False := fun hb ↦
      ((SimpleGraph.compl_adj _ _ _).1 (hblue _ hb _ hr (by simp))).2
        (b_x_red data _ (c0_ne_c2 data).symm r)
    have hinjXY : ∀ σ, (∀ g g', core g ∈ t → core g' ∈ t → g = g') →
        (∀ g q, core g ∈ t → x data.cert (some q) ∈ t → σ ≠ q) →
        (∀ g q, core g ∈ t → y data.cert (some q) ∈ t → σ ≠ q) →
        (∀ g, core g ∈ t → z ∈ t → σ ≠ i0Index data) →
        (∀ g, core g ∈ t → w ∈ t → σ ≠ i0Index data) →
        Set.InjOn (slotXY data σ) t := by
      intro σ hc0 hc1 hc2 hc3 hc4 u₁ hu₁ u₂ hu₂ heq
      by_contra hne
      have hb := hblue _ hu₁ _ hu₂ hne
      rcases hmem u₁ hu₁ with ⟨g₁, -, -, -, rfl⟩ | ⟨p₁, -, rfl⟩ | rfl | ⟨q₁, hq₁, rfl⟩ |
          ⟨q₁, rfl⟩ | rfl | rfl <;>
        rcases hmem u₂ hu₂ with ⟨g₂, -, -, -, rfl⟩ | ⟨p₂, -, rfl⟩ | rfl | ⟨q₂, hq₂, rfl⟩ |
          ⟨q₂, rfl⟩ | rfl | rfl <;>
        (try simp only [slotXY_core, slotXY_x, slotXY_y, slotXY_z, slotXY_w, slotXY_a,
          slotXY_b] at heq) <;>
        first
        | exact hne rfl
        | exact (hna _ hu₁).elim
        | exact (hna _ hu₂).elim
        | exact (hnb hu₁).elim
        | exact (hnb hu₂).elim
        | exact hne (by rw [hc0 g₁ g₂ hu₁ hu₂])
        | exact hc1 g₁ q₂ hu₁ hu₂ heq
        | exact hc1 g₂ q₁ hu₂ hu₁ heq.symm
        | exact hc2 g₁ q₂ hu₁ hu₂ heq
        | exact hc2 g₂ q₁ hu₂ hu₁ heq.symm
        | exact hc3 g₁ hu₁ hu₂ heq
        | exact hc3 g₂ hu₂ hu₁ heq.symm
        | exact hc4 g₁ hu₁ hu₂ heq
        | exact hc4 g₂ hu₂ hu₁ heq.symm
        | exact hq₁ heq
        | exact hq₂ heq.symm
        | (subst heq; exact hne rfl)
        | (subst heq; simp [SimpleGraph.compl_adj] at hb; done)
        | (subst heq; exact ((SimpleGraph.compl_adj _ _ _).1 hb).2 (y0_z_red data))
        | (subst heq; exact ((SimpleGraph.compl_adj _ _ _).1 hb).2 (y0_z_red data).symm)
        | (subst heq; exact ((SimpleGraph.compl_adj _ _ _).1 hb).2 (y0_w_red data))
        | (subst heq; exact ((SimpleGraph.compl_adj _ _ _).1 hb).2 (y0_w_red data).symm)
        | exact (nB_z_w data hb).elim
        | exact (nB_z_w data hb.symm).elim
    by_cases hcore : ∃ v, core v ∈ t
    · obtain ⟨v₀, hv₀⟩ := hcore
      have hcoreI : ∀ v, core v ∈ t → v = data.cert.i r := by
        intro v hv
        have hb := hblue _ hv _ hr (by simp)
        rw [SimpleGraph.compl_adj, old_adj_core_x_some] at hb
        by_contra hvr
        exact hb.2 ⟨fun h ↦ hvr h.symm, fun _ ↦ hr0⟩
      have hxI : ∀ q, x data.cert (some q) ∈ t → q = r := by
        intro q hq
        have hv := hcoreI v₀ hv₀
        by_contra hqr
        have hb := hblue _ hv₀ _ hq (by simp)
        rw [SimpleGraph.compl_adj, old_adj_core_x_some] at hb
        exact hb.2 ⟨fun h ↦ hqr (data.cert.i.injective (h.trans hv)),
          fun h ↦ (data.cert.c_ne_i _ _ (h.symm.trans hv)).elim⟩
      have hmem' : ∀ u ∈ t, u = core (data.cert.i r) ∨ u = x data.cert (some r) ∨
          (∃ q, u = y data.cert (some q)) ∨ u = z ∨ u = w := by
        intro u hu
        rcases hmem u hu with ⟨g, -, -, -, rfl⟩ | ⟨p, -, rfl⟩ | rfl | ⟨q, -, rfl⟩ | ⟨q, rfl⟩ |
            rfl | rfl
        · exact Or.inl (by rw [hcoreI g hu])
        · exact (hna p hu).elim
        · exact (hnb hu).elim
        · exact Or.inr (Or.inl (by rw [hxI q hu]))
        · exact Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      have hred_of : ∀ u v, u ∈ t → v ∈ t → u ≠ v → (oldGraph data).Adj u v → False :=
        fun u v hu hv huv h ↦ ((SimpleGraph.compl_adj _ _ _).1 (hblue u hu v hv huv)).2 h
      by_cases hy0 : y data.cert (some (i0Index data)) ∈ t
      · -- `y₀ ∈ t`: no `z`, no `w`, the `y` are among `y₀, y₁, y₂`
        have hz : z ∉ t := fun hz ↦ hred_of _ _ hy0 hz (by simp) (y0_z_red data)
        have hw : w ∉ t := fun hw ↦ hred_of _ _ hy0 hw (by simp) (y0_w_red data)
        have hy : ∀ q, y data.cert (some q) ∈ t →
            q = i0Index data ∨ q = Switching.Vertex.i1 data.cert ∨ q = i2Index data := by
          intro q hq
          rcases q_cases data q with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact (hred_of _ _ hy0 hq (y_some_ne data (fun e ↦ by
              have := congrArg Fin.val e; omega)) (y0_red_high data hE h)).elim
        by_cases hy2 : y data.cert (some (i2Index data)) ∈ t
        · have hsub4 : t ⊆ {core (data.cert.i r), x data.cert (some r),
              y data.cert (some (i0Index data)), y data.cert (some (i2Index data))} := by
            intro u hu
            rcases hmem' u hu with rfl | rfl | ⟨q, rfl⟩ | rfl | rfl
            · simp
            · simp
            · rcases hy q hu with rfl | rfl | rfl
              · simp
              · exact (hred_of _ _ hu hy2 (y_some_ne data (fun e ↦ by
                  have := congrArg Fin.val e; omega)) (y1_red_high data hE (by omega))).elim
              · simp
            · exact (hz hu).elim
            · exact (hw hu).elim
          have := (Finset.card_le_card hsub4).trans Finset.card_le_four
          rw [ht.card_eq] at this
          omega
        · have hsub4 : t ⊆ {core (data.cert.i r), x data.cert (some r),
              y data.cert (some (i0Index data)),
              y data.cert (some (Switching.Vertex.i1 data.cert))} := by
            intro u hu
            rcases hmem' u hu with rfl | rfl | ⟨q, rfl⟩ | rfl | rfl
            · simp
            · simp
            · rcases hy q hu with rfl | rfl | rfl
              · simp
              · simp
              · exact (hy2 hu).elim
            · exact (hz hu).elim
            · exact (hw hu).elim
          have := (Finset.card_le_card hsub4).trans Finset.card_le_four
          rw [ht.card_eq] at this
          omega
      · by_cases hy1 : y data.cert (some (Switching.Vertex.i1 data.cert)) ∈ t
        · -- `y₁ ∈ t`, `y₀ ∉ t`: the only `y` is `y₁`; `z`, `w` not both
          have hy : ∀ q, y data.cert (some q) ∈ t → q = Switching.Vertex.i1 data.cert := by
            intro q hq
            rcases q_cases data q with h | h | h | h
            · exact (hy0 (h ▸ hq)).elim
            · exact h
            · subst h
              exact (hred_of _ _ hy1 hq (y_some_ne data (fun e ↦ by
                have := congrArg Fin.val e; omega)) (y1_red_high data hE (by omega))).elim
            · exact (hred_of _ _ hy1 hq (y_some_ne data (fun e ↦ by
                have := congrArg Fin.val e; omega)) (y1_red_high data hE (by omega))).elim
          by_cases hw : w ∈ t
          · have hz : z ∉ t := fun hz ↦ (nB_z_w data (hblue _ hz _ hw (by simp)))
            have hsub4 : t ⊆ {core (data.cert.i r), x data.cert (some r),
                y data.cert (some (Switching.Vertex.i1 data.cert)), w} := by
              intro u hu
              rcases hmem' u hu with rfl | rfl | ⟨q, rfl⟩ | rfl | rfl
              · simp
              · simp
              · rw [hy q hu]
                simp
              · exact (hz hu).elim
              · simp
            have := (Finset.card_le_card hsub4).trans Finset.card_le_four
            rw [ht.card_eq] at this
            omega
          · have hsub4 : t ⊆ {core (data.cert.i r), x data.cert (some r),
                y data.cert (some (Switching.Vertex.i1 data.cert)), z} := by
              intro u hu
              rcases hmem' u hu with rfl | rfl | ⟨q, rfl⟩ | rfl | rfl
              · simp
              · simp
              · rw [hy q hu]
                simp
              · simp
              · exact (hw hu).elim
            have := (Finset.card_le_card hsub4).trans Finset.card_le_four
            rw [ht.card_eq] at this
            omega
        · -- every `y` of the clique has index at least `2`: a free slot for `i_r`
          let σ : Fin (s - 1) :=
            if r ≠ Switching.Vertex.i1 data.cert then Switching.Vertex.i1 data.cert
            else if w ∈ t then i2Index data else i0Index data
          have hσr : σ ≠ r := by
            simp only [σ]
            split_ifs with h1 h2
            · exact fun h ↦ h1 h.symm
            · intro h
              have := congrArg Fin.val h
              push_neg at h1
              rw [h1] at this
              omega
            · intro h
              push_neg at h1
              rw [h1] at h
              exact h01 h
          have hσy : ∀ q, y data.cert (some q) ∈ t → σ ≠ q := by
            intro q hq
            have hq0 : q ≠ i0Index data := fun h ↦ hy0 (h ▸ hq)
            have hq1 : q ≠ Switching.Vertex.i1 data.cert := fun h ↦ hy1 (h ▸ hq)
            simp only [σ]
            split_ifs with h1 h2
            · exact fun h ↦ hq1 h.symm
            · rintro rfl
              exact hred_of _ _ hq h2 (by simp) (y2_w_red data)
            · exact fun h ↦ hq0 h.symm
          have hσz : z ∈ t → σ ≠ i0Index data := by
            intro hz
            simp only [σ]
            split_ifs with h1 h2
            · exact fun h ↦ h01 h.symm
            · intro h
              have := congrArg Fin.val h
              omega
            · intro _
              push_neg at h1
              rw [h1] at hr
              exact hred_of _ _ hr hz (by simp) (x1_z_red data)
          have hσw : w ∈ t → σ ≠ i0Index data := by
            intro hw
            simp only [σ]
            split_ifs with h1 h2
            · exact fun h ↦ h01 h.symm
            · intro h
              have := congrArg Fin.val h
              omega
          have hinj := hinjXY σ (fun g g' hg hg' ↦ (hcoreI g hg).trans (hcoreI g' hg').symm)
            (fun g q _ hq ↦ by rw [hxI q hq]; exact hσr)
            (fun g q _ hq ↦ hσy q hq)
            (fun g _ hz ↦ hσz hz)
            (fun g _ hw ↦ hσw hw)
          have := card_le_of_slot (slotXY data σ) hinj
          rw [ht.card_eq] at this
          omega
    · -- no core vertex: `x_q, y_q ↦ q`, `z, w ↦ 0`
      have hinj := hinjXY (i0Index data) (fun g _ hg _ ↦ (hcore ⟨g, hg⟩).elim)
        (fun g _ hg _ ↦ (hcore ⟨g, hg⟩).elim) (fun g _ hg _ ↦ (hcore ⟨g, hg⟩).elim)
        (fun g hg _ ↦ (hcore ⟨g, hg⟩).elim) (fun g hg _ ↦ (hcore ⟨g, hg⟩).elim)
      have := card_le_of_slot (slotXY data (i0Index data)) hinj
      rw [ht.card_eq] at this
      omega
  · -- III.1, III.3: no `x`; project to a blue clique of `G`
    refine false_of_projection hG.2 ht (projBlue data (b (c2Index data) ∈ t)) ?_
    intro u hu v hv huv
    have hb := hblue u hu v hv huv
    rcases hmem u hu with ⟨g, hgC, hgi, hgG, rfl⟩ | ⟨p, hp, rfl⟩ | rfl | ⟨q, hq, rfl⟩ |
        ⟨q, rfl⟩ | rfl | rfl <;>
      rcases hmem v hv with ⟨g', hgC', hgi', hgG', rfl⟩ | ⟨p', hp', rfl⟩ | rfl | ⟨q', hq', rfl⟩ |
        ⟨q', rfl⟩ | rfl | rfl <;>
      (try simp only [projBlue_core, projBlue_a, projBlue_b, projBlue_y, projBlue_w]) <;>
      first
      | exact (hx ⟨_, hu⟩).elim
      | exact (hx ⟨_, hv⟩).elim
      | exact (huv rfl).elim
      | exact pB_core_core data hb
      | exact pB_core_i0 data hgi hgG
      | exact (pB_core_i0 data hgi' hgG').symm
      | exact pB_core_b2 data hgC hb
      | exact (pB_core_b2 data hgC' hb.symm).symm
      | exact pB_core_y data hb
      | exact (pB_core_y data hb.symm).symm
      | exact pB_core_z data hgC hgi hgG hb
      | exact (pB_core_z data hgC' hgi' hgG' hb.symm).symm
      | exact pB_a_y data hp hb
      | exact (pB_a_y data hp' hb.symm).symm
      | exact pB_b2_y data hb
      | exact (pB_b2_y data hb.symm).symm
      | (rw [projBlue_z, if_pos hu]; exact pB_b2_i0 data)
      | (rw [projBlue_z, if_pos hv]; exact (pB_b2_i0 data).symm)
      | exact pB_b2_i0 data
      | exact (pB_b2_i0 data).symm
      | exact pB_y_y data huv
      | exact pB_y_z data hb
      | exact (pB_y_z data hb.symm).symm
      | exact pB_y_w data hb
      | exact (pB_y_w data hb.symm).symm
      | exact (nB_a_a data hb).elim
      | exact (nB_a_b2 data hp hb).elim
      | exact (nB_a_b2 data hp' hb.symm).elim
      | exact (nB_a_z data hp hb).elim
      | exact (nB_a_z data hp' hb.symm).elim
      | exact (nB_a_w data hp hb).elim
      | exact (nB_a_w data hp' hb.symm).elim
      | exact (nB_z_w data hb).elim
      | exact (nB_z_w data hb.symm).elim

end

end ThirdConnector
end RamseyIncrement
