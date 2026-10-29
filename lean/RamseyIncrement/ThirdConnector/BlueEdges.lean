/-
Rule R*, Part I (1) and (2): the two switched edges that became blue.
-/
import RamseyIncrement.ThirdConnector.ColourTable

/-!
# Part I (1), (2): the blue switched edges

`c₂x₀` and `i₀x_*` are blue after R*.  A blue `K_(s+1)` through either edge
would leave a blue `K_(s-1)` in the common blue neighborhood `Z` of its
endpoints.  We compute `Z` from the colour table and show that a blue clique
in `Z` has at most `s - 2` vertices; (P2) supplies the missing index.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

section

variable (data : Certificates.PlusCaseAData G k s)

theorem i0_ne_i1 : i0Index data ≠ Switching.Vertex.i1 data.cert := by
  intro h
  have := congrArg Fin.val h
  simp [SecondConnector.TypeA.i0Index, Switching.Vertex.i1, Certificates.i0Index',
    Certificates.i1Index', Certificates.indexZero, Certificates.indexOne] at this

theorem c0_ne_c2 : c0Index data ≠ c2Index data := by
  intro h
  have := congrArg Fin.val h
  simp [SecondConnector.TypeA.c0Index, SecondConnector.TypeA.c2Index, Certificates.c0Index,
    Certificates.c2Index, Certificates.indexZero] at this

/-- Every vertex of `H⁺` is one of the named vertices. -/
theorem vertex_cases (u : SecondConnector.Vertex V k s) :
    (∃ v, u = core v) ∨ (∃ p, u = a p) ∨ (∃ p, u = b p) ∨
      (∃ r, u = x data.cert r) ∨ (∃ r, u = y data.cert r) ∨ u = z ∨ u = w := by
  rcases u with u | u
  · rcases SecondConnector.vertex_six_block_cases data.cert u with
      ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl
    · exact Or.inl ⟨v, rfl⟩
    · exact Or.inr (Or.inl ⟨p, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · cases u
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- I(1): the common blue neighborhood of `c₂` and `x₀` is
`{i₀, x_*, y_*} ∪ {y_q : q ≠ 0, c₂i_q blue}`. -/
theorem mem_blue_common_c2_x0 (hE : data.cert.E = ∅)
    {u : SecondConnector.Vertex V k s}
    (hu : u ∈ (oldGraph data)ᶜ.commonNeighbors (core (data.cert.c (c2Index data)))
      (x data.cert (some (i0Index data)))) :
    u = core (data.cert.i (i0Index data)) ∨ u = x data.cert none ∨ u = y data.cert none ∨
      ∃ q, q ≠ i0Index data ∧ ¬G.Adj (data.cert.c (c2Index data)) (data.cert.i q) ∧
        u = y data.cert (some q) := by
  rw [SimpleGraph.mem_commonNeighbors, SimpleGraph.compl_adj, SimpleGraph.compl_adj] at hu
  obtain ⟨⟨hne1, hb1⟩, ⟨hne2, hb2⟩⟩ := hu
  rcases vertex_cases data u with ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl | rfl
  · simp at hb2 hne1
    left
    by_contra h
    simp at h
    exact hne1 (hb2 (Ne.symm h)).symm
  · simp [hE] at hb2
  · simp [i0_ne_i1] at hb2
  · cases r with
    | none => exact Or.inr (Or.inl rfl)
    | some q =>
        have hci := data.cert.c_ne_i (c2Index data) q
        simp at hb1 hne2
        exact absurd (hb1 (Ne.symm hci)).symm hne2
  · cases r with
    | none => exact Or.inr (Or.inr (Or.inl rfl))
    | some q =>
        simp at hb1 hb2
        refine Or.inr (Or.inr (Or.inr ⟨q, Ne.symm hb2, fun h ↦ hb1.2 h.symm, rfl⟩))
  · simp at hb1
    exact (hb1 (c0_ne_c2 data).symm (data.cert.c_adj (c0_ne_c2 data))).elim
  · simp [SecondConnector.TypeA.redToWA_core] at hb1

/-- Slots for the counting argument: `y_q ↦ q`, every `x` and `y_* ↦ 1`,
everything else `↦ 0`. -/
noncomputable def slotY : SecondConnector.Vertex V k s → Fin (s - 1)
  | .inl (.inl (.b r)) =>
      (Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r).getD
        (Switching.Vertex.i1 data.cert)
  | .inl (.inl (.a _)) => Switching.Vertex.i1 data.cert
  | _ => i0Index data

@[simp] theorem slotY_y_some (q : Fin (s - 1)) : slotY data (y data.cert (some q)) = q := by
  simp [slotY]

@[simp] theorem slotY_y_none : slotY data (y data.cert none) = Switching.Vertex.i1 data.cert := by
  simp [slotY]

@[simp] theorem slotY_x (r : Option (Fin (s - 1))) :
    slotY data (x data.cert r) = Switching.Vertex.i1 data.cert := rfl

@[simp] theorem slotY_core (v : V) : slotY data (core v) = i0Index data := rfl

@[simp] theorem slotY_a (p : Fin (k - 1)) : slotY data (a p) = i0Index data := rfl

/-- I(1): no blue `K_(s-1)` in the common blue neighborhood of `c₂` and `x₀`. -/
theorem blue_common_c2_x0_cliqueFree (hE : data.cert.E = ∅) (hP2 : P2 data) :
    (oldGraph data)ᶜ.CliqueFreeOn
      ((oldGraph data)ᶜ.commonNeighbors (core (data.cert.c (c2Index data)))
        (x data.cert (some (i0Index data)))) (s - 1) := by
  classical
  intro t hsub ht
  have hs := data.cert.five_le_s
  have hmem : ∀ u ∈ t, _ := fun u hu ↦ mem_blue_common_c2_x0 data hE (hsub hu)
  have hblue : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data)ᶜ.Adj u v :=
    fun u hu v hv huv ↦ ht.isClique hu hv huv
  obtain ⟨r, hr2, hrred⟩ := hP2
  have h01 := i0_ne_i1 data
  by_cases hy1 : y data.cert (some (Switching.Vertex.i1 data.cert)) ∈ t
  · have hsub3 : t ⊆ {core (data.cert.i (i0Index data)), x data.cert none,
        y data.cert (some (Switching.Vertex.i1 data.cert))} := by
      intro u hu
      rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, hq, rfl⟩
      · simp
      · simp
      · exfalso
        have h := hblue _ hu _ hy1 (by simp)
        simp [hE, YLow, Switching.SymmPair, Switching.Vertex.i1] at h
        exact h01 h.symm
      · by_cases hq1 : q = Switching.Vertex.i1 data.cert
        · subst hq1
          simp
        · exfalso
          have hq0' : q.val ≠ 0 := fun h ↦ hq0 (Fin.ext (by simpa using h))
          have hq1' : q.val ≠ 1 := fun h ↦ hq1 (Fin.ext (by simpa [Switching.Vertex.i1] using h))
          have h := hblue _ hu _ hy1 (by simpa using hq1)
          rw [SimpleGraph.compl_adj] at h
          apply h.2
          have v0 : (i0Index data).val = 0 := rfl
          have v1 : (Switching.Vertex.i1 data.cert).val = 1 := rfl
          have v2 : (i2Index data).val = 2 := rfl
          rw [old_adj_y_y data hE]
          refine ⟨by simpa using hq1, ?_, ?_, ?_⟩
          · simp only [YLow, v1]
            omega
          · simp [Switching.SymmPair, hq0]
          · simp only [Switching.SymmPair, Option.some.injEq, not_or, not_and]
            refine ⟨fun _ h ↦ ?_, fun _ h ↦ ?_⟩ <;>
              have := congrArg Fin.val h <;> omega
    have hc := Finset.card_le_card hsub3
    have h3 : ({core (data.cert.i (i0Index data)), x data.cert none,
        y data.cert (some (Switching.Vertex.i1 data.cert))} :
          Finset (SecondConnector.Vertex V k s)).card ≤ 3 := Finset.card_le_three
    rw [ht.card_eq] at hc
    omega
  · have hmaps : Set.MapsTo (slotY data) t (Finset.univ.erase r) := by
      intro u hu
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and]
      rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, hq, rfl⟩
      · intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp [Switching.Vertex.i1] at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp [Switching.Vertex.i1] at this
        omega
      · intro h
        simp only [slotY_y_some] at h
        subst h
        exact hq hrred
    have hinj : Set.InjOn (slotY data) t := by
      intro u₁ hu₁ u₂ hu₂ heq
      by_contra hne
      have hb := hblue _ hu₁ _ hu₂ hne
      rcases hmem u₁ hu₁ with rfl | rfl | rfl | ⟨q₁, hq₁, -, rfl⟩ <;>
        rcases hmem u₂ hu₂ with rfl | rfl | rfl | ⟨q₂, hq₂, -, rfl⟩ <;>
        simp only [slotY_core, slotY_x, slotY_y_none, slotY_y_some] at heq <;>
        first
        | exact hne rfl
        | exact h01 heq
        | exact h01 heq.symm
        | exact hq₂ heq.symm
        | exact hq₁ heq
        | (subst heq; exact hy1 hu₂)
        | (subst heq; exact hy1 hu₁)
        | (subst heq; exact hne rfl)
        | (simp at hb)
    have hc := Finset.card_le_card_of_injOn (slotY data) hmaps hinj
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin,
      ht.card_eq] at hc
    omega

/-- I(2): the common blue neighborhood of `i₀` and `x_*` is
`{c₂, a₀, x₀} ∪ {y_q : q ≠ 0}`. -/
theorem mem_blue_common_i0_xStar (hE : data.cert.E = ∅) (hP1 : P1 data)
    {u : SecondConnector.Vertex V k s}
    (hu : u ∈ (oldGraph data)ᶜ.commonNeighbors (core (data.cert.i (i0Index data)))
      (x data.cert none)) :
    u = core (data.cert.c (c2Index data)) ∨ u = a (c0Index data) ∨
      u = x data.cert (some (i0Index data)) ∨ ∃ q, q ≠ i0Index data ∧ u = y data.cert (some q) := by
  rw [SimpleGraph.mem_commonNeighbors, SimpleGraph.compl_adj, SimpleGraph.compl_adj] at hu
  obtain ⟨⟨hne1, hb1⟩, ⟨hne2, hb2⟩⟩ := hu
  rcases vertex_cases data u with ⟨v, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl | rfl
  · left
    rw [P1] at hP1
    simp [hP1] at hb2 hne1
    by_contra h
    simp at h
    exact hne1 (hb2 h).symm
  · right; left
    simp [hE] at hb2
    rw [hb2]
  · exfalso
    simp at hb2
    subst hb2
    simp at hb1
    exact hb1 (fun h ↦ data.cert.c_ne_i _ _ h.symm) data.c0_i0_red
  · cases r with
    | none => exact absurd rfl hne2
    | some q =>
        right; right; left
        have hic : data.cert.i (i0Index data) ≠ data.cert.c (c2Index data) :=
          fun h ↦ data.cert.c_ne_i _ _ h.symm
        simp [hic] at hb1
        rw [hb1]
  · cases r with
    | none => simp at hb2
    | some q =>
        right; right; right
        simp at hb1
        exact ⟨q, fun h ↦ hb1.1 (by rw [h]), rfl⟩
  · simp at hb2
  · simp at hb2

/-- Slots for I(2): `y_q ↦ q`, core vertices `↦ 1`, everything else `↦ 0`. -/
noncomputable def slotX : SecondConnector.Vertex V k s → Fin (s - 1)
  | .inl (.inl (.b r)) =>
      (Canonical.outerIndexEquiv (le_trans (by decide : 1 ≤ 5) data.cert.five_le_s) r).getD
        (Switching.Vertex.i1 data.cert)
  | .inl (.inl (.core (.core _))) => Switching.Vertex.i1 data.cert
  | _ => i0Index data

@[simp] theorem slotX_y_some (q : Fin (s - 1)) : slotX data (y data.cert (some q)) = q := by
  simp [slotX]

@[simp] theorem slotX_core (v : V) : slotX data (core v) = Switching.Vertex.i1 data.cert := rfl

@[simp] theorem slotX_a (p : Fin (k - 1)) : slotX data (a p) = i0Index data := rfl

@[simp] theorem slotX_x (r : Option (Fin (s - 1))) : slotX data (x data.cert r) = i0Index data :=
  rfl

/-- I(2): no blue `K_(s-1)` in the common blue neighborhood of `i₀` and `x_*`. -/
theorem blue_common_i0_xStar_cliqueFree (hE : data.cert.E = ∅) (hP1 : P1 data) (hP2 : P2 data) :
    (oldGraph data)ᶜ.CliqueFreeOn
      ((oldGraph data)ᶜ.commonNeighbors (core (data.cert.i (i0Index data)))
        (x data.cert none)) (s - 1) := by
  classical
  intro t hsub ht
  have hs := data.cert.five_le_s
  have hmem : ∀ u ∈ t, _ := fun u hu ↦ mem_blue_common_i0_xStar data hE hP1 (hsub hu)
  have hblue : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data)ᶜ.Adj u v :=
    fun u hu v hv huv ↦ ht.isClique hu hv huv
  obtain ⟨r, hr2, hrred⟩ := hP2
  have h01 := i0_ne_i1 data
  have v0 : (i0Index data).val = 0 := rfl
  have v1 : (Switching.Vertex.i1 data.cert).val = 1 := rfl
  have v2 : (i2Index data).val = 2 := rfl
  -- `a₀` and `x₀` are red to each other
  have hax : ¬(a (c0Index data) ∈ t ∧ x data.cert (some (i0Index data)) ∈ t) := by
    rintro ⟨ha, hx⟩
    have h := hblue _ ha _ hx (by simp)
    simp [hE] at h
  by_cases hy1 : y data.cert (some (Switching.Vertex.i1 data.cert)) ∈ t
  · -- then no other `y` is in `t`, and `t` has at most three vertices
    have hy : ∀ q, q ≠ i0Index data → y data.cert (some q) ∈ t → q = Switching.Vertex.i1 data.cert := by
      intro q hq0 hq
      by_contra hq1
      have h := hblue _ hq _ hy1 (by simpa using hq1)
      rw [SimpleGraph.compl_adj] at h
      apply h.2
      rw [old_adj_y_y data hE]
      have hq0' : q.val ≠ 0 := fun h ↦ hq0 (Fin.ext (by omega))
      have hq1' : q.val ≠ 1 := fun h ↦ hq1 (Fin.ext (by omega))
      refine ⟨by simpa using hq1, ?_, ?_, ?_⟩
      · simp only [YLow, v1]
        omega
      · simp [Switching.SymmPair, hq0]
      · simp only [Switching.SymmPair, Option.some.injEq, not_or, not_and]
        refine ⟨fun _ h ↦ ?_, fun _ h ↦ ?_⟩ <;> have := congrArg Fin.val h <;> omega
    have hsub3 : t ⊆ {core (data.cert.c (c2Index data)), a (c0Index data),
        y data.cert (some (Switching.Vertex.i1 data.cert))} ∨
        t ⊆ {core (data.cert.c (c2Index data)), x data.cert (some (i0Index data)),
        y data.cert (some (Switching.Vertex.i1 data.cert))} := by
      by_cases hxt : x data.cert (some (i0Index data)) ∈ t
      · right
        intro u hu
        rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, rfl⟩
        · simp
        · exact absurd ⟨hu, hxt⟩ hax
        · simp
        · rw [hy q hq0 hu]
          simp
      · left
        intro u hu
        rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, rfl⟩
        · simp
        · simp
        · exact absurd hu hxt
        · rw [hy q hq0 hu]
          simp
    rcases hsub3 with h3 | h3 <;>
    · have hc := (Finset.card_le_card h3).trans Finset.card_le_three
      rw [ht.card_eq] at hc
      omega
  · -- slots: `c₂ ↦ 1`, `a₀, x₀ ↦ 0`, `y_q ↦ q`
    have hinj : Set.InjOn (slotX data) t := by
      intro u₁ hu₁ u₂ hu₂ heq
      by_contra hne
      rcases hmem u₁ hu₁ with rfl | rfl | rfl | ⟨q₁, hq₁, rfl⟩ <;>
        rcases hmem u₂ hu₂ with rfl | rfl | rfl | ⟨q₂, hq₂, rfl⟩ <;>
        simp only [slotX_core, slotX_x, slotX_a, slotX_y_some] at heq <;>
        first
        | exact hne rfl
        | exact h01 heq
        | exact h01 heq.symm
        | exact hq₂ heq.symm
        | exact hq₁ heq
        | exact hax ⟨hu₁, hu₂⟩
        | exact hax ⟨hu₂, hu₁⟩
        | (subst heq; exact hy1 hu₂)
        | (subst heq; exact hy1 hu₁)
        | (subst heq; exact hne rfl)
    by_cases hc2 : core (data.cert.c (c2Index data)) ∈ t
    · have hmaps : Set.MapsTo (slotX data) t (Finset.univ.erase r) := by
        intro u hu
        simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and]
        rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, rfl⟩
        · intro h; have := congrArg Fin.val h; simp only [slotX_core] at this; omega
        · intro h; have := congrArg Fin.val h; simp only [slotX_a] at this; omega
        · intro h; have := congrArg Fin.val h; simp only [slotX_x] at this; omega
        · intro h
          simp only [slotX_y_some] at h
          subst h
          have hb := hblue _ hc2 _ hu (by simp)
          simp at hb
          exact hb.2 hrred.symm
      have hc := Finset.card_le_card_of_injOn (slotX data) hmaps hinj
      rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin,
        ht.card_eq] at hc
      omega
    · have hmaps : Set.MapsTo (slotX data) t (Finset.univ.erase (Switching.Vertex.i1 data.cert)) := by
        intro u hu
        simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and]
        rcases hmem u hu with rfl | rfl | rfl | ⟨q, hq0, rfl⟩
        · exact absurd hu hc2
        · simp only [slotX_a]; exact h01
        · simp only [slotX_x]; exact h01
        · intro h
          simp only [slotX_y_some] at h
          subst h
          exact hy1 hu
      have hc := Finset.card_le_card_of_injOn (slotX data) hmaps hinj
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        ht.card_eq] at hc
      omega

end

end ThirdConnector
end RamseyIncrement
