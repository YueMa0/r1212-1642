/-
Rule R*, Part I (3): the switched edges `a_p y₀` (`p` odd) that became red.
-/
import RamseyIncrement.ThirdConnector.BlueEdges

/-!
# Part I (3): the red switched edges

For odd `p` the edge `a_p y₀` is red after R*.  Its common red neighborhood
`Z` lies in `{c_p, z, w, x₀} ∪ {a_q} ∪ {b_q}` with `q ≠ p`.  Send `a_q, b_q, c_p`
to their index, `x₀` and `w` to `2`, and `z` to `0`.  Two vertices with the
same index are blue to each other, so a red clique in `Z` injects into the
indices `0, …, k-2`, and it misses the index `p` unless it contains `c_p`.
-/

namespace RamseyIncrement
namespace ThirdConnector

open SimpleGraph
open SecondConnector.TypeA (c0Index c1Index c2Index i0Index i2Index P Q)

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

section

variable (data : Certificates.PlusCaseAData G k s)

theorem c_val_ne_of_odd {p : Fin (k - 1)} (hp : p.val % 2 = 1) :
    p ≠ c0Index data ∧ p ≠ c2Index data := by
  constructor <;> intro h <;> have := congrArg Fin.val h <;>
    simp [SecondConnector.TypeA.c0Index, SecondConnector.TypeA.c2Index, Certificates.c0Index,
      Certificates.c2Index, Certificates.indexZero] at this <;> omega

/-- I(3): the common red neighborhood of `a_p` and `y₀` for odd `p`. -/
theorem mem_red_common_ap_y0 (hE : data.cert.E = ∅) {p : Fin (k - 1)} (hp : p.val % 2 = 1)
    {u : SecondConnector.Vertex V k s}
    (hu : u ∈ (oldGraph data).commonNeighbors (a p) (y data.cert (some (i0Index data)))) :
    u = core (data.cert.c p) ∨ (∃ q, q ≠ p ∧ (q = c0Index data ∨ q.val % 2 = 1) ∧ u = a q) ∨
      (∃ q, q ≠ p ∧ q ≠ c0Index data ∧ q ≠ c2Index data ∧ u = b q) ∨
      u = x data.cert (some (i0Index data)) ∨ u = z ∨ u = w := by
  rw [SimpleGraph.mem_commonNeighbors] at hu
  obtain ⟨h1, h2⟩ := hu
  obtain ⟨hp0, hp2⟩ := c_val_ne_of_odd data hp
  have hT : i0Index data ∈ data.cert.T := by
    rw [Certificates.OrderedCertificates.mem_T]
    exact data.c0_i0_red
  rcases vertex_cases data u with ⟨v, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl | rfl
  · left
    simp [hp2] at h1
    rw [h1]
  · right; left
    simp at h1 h2
    refine ⟨q, Ne.symm h1, ?_, rfl⟩
    rcases h2 with ⟨-, h⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  · right; right; left
    simp at h1 h2
    refine ⟨q, Ne.symm h1, h2.1, fun hq ↦ ?_, rfl⟩
    subst hq
    exact data.c2_i0_blue h2.2
  · right; right; right; left
    simp at h2
    rw [h2]
  · exfalso
    cases r with
    | none =>
        rw [old_adj_y_y data hE] at h2
        simp [YLow, Switching.SymmPair] at h2
    | some q =>
        simp [hp0] at h1
        obtain ⟨-, h1⟩ := h1
        subst h1
        exact (oldGraph data).loopless.irrefl _ h2
  · right; right; right; right; left; rfl
  · right; right; right; right; right; rfl

theorem a_index_ne_c2 {q : Fin (k - 1)} (hq : q = c0Index data ∨ q.val % 2 = 1) :
    q ≠ c2Index data := by
  rintro rfl
  rcases hq with h | h
  · exact c0_ne_c2 data h.symm
  · simp [SecondConnector.TypeA.c2Index, Certificates.c2Index] at h

/-- Slots for I(3): `a_q, b_q ↦ q`, core vertices `↦ p`, `x` and `w ↦ 2`,
`z` (and `y`) `↦ 0`. -/
noncomputable def slotA (p : Fin (k - 1)) : SecondConnector.Vertex V k s → Fin (k - 1)
  | .inl (.inl (.core (.a q))) => q
  | .inl (.inl (.core (.b q))) => q
  | .inl (.inl (.core (.core _))) => p
  | .inl (.inl (.a _)) => c2Index data
  | .inr _ => c2Index data
  | _ => c0Index data

@[simp] theorem slotA_a (p q : Fin (k - 1)) : slotA data p (a q) = q := rfl
@[simp] theorem slotA_b (p q : Fin (k - 1)) : slotA data p (b q) = q := rfl
@[simp] theorem slotA_core (p : Fin (k - 1)) (v : V) : slotA data p (core v) = p := rfl
@[simp] theorem slotA_x (p : Fin (k - 1)) (r : Option (Fin (s - 1))) :
    slotA data p (x data.cert r) = c2Index data := rfl
@[simp] theorem slotA_w (p : Fin (k - 1)) : slotA data p w = c2Index data := rfl
@[simp] theorem slotA_z (p : Fin (k - 1)) : slotA data p z = c0Index data := rfl

/-- I(3): no red `K_(k-1)` in the common red neighborhood of `a_p` and `y₀`. -/
theorem red_common_ap_y0_cliqueFree (hE : data.cert.E = ∅) {p : Fin (k - 1)}
    (hp : p.val % 2 = 1) :
    (oldGraph data).CliqueFreeOn
      ((oldGraph data).commonNeighbors (a p) (y data.cert (some (i0Index data)))) (k - 1) := by
  classical
  intro t hsub ht
  have hk := data.cert.five_le_k
  have hmem : ∀ u ∈ t, _ := fun u hu ↦ mem_red_common_ap_y0 data hE hp (hsub hu)
  have hred : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (oldGraph data).Adj u v :=
    fun u hu v hv huv ↦ ht.isClique hu hv huv
  obtain ⟨hp0, hp2⟩ := c_val_ne_of_odd data hp
  have h02 := c0_ne_c2 data
  have hinj : Set.InjOn (slotA data p) t := by
    intro u₁ hu₁ u₂ hu₂ heq
    by_contra hne
    have hr := hred _ hu₁ _ hu₂ hne
    rcases hmem u₁ hu₁ with rfl | ⟨q₁, hq₁p, hq₁, rfl⟩ | ⟨q₁, hq₁p, hq₁0, hq₁2, rfl⟩ | rfl | rfl | rfl <;>
      rcases hmem u₂ hu₂ with rfl | ⟨q₂, hq₂p, hq₂, rfl⟩ | ⟨q₂, hq₂p, hq₂0, hq₂2, rfl⟩ | rfl | rfl | rfl <;>
      simp only [slotA_a, slotA_b, slotA_core, slotA_x, slotA_w, slotA_z] at heq <;>
      first
      | exact hne rfl
      | exact hq₂p heq.symm
      | exact hq₁p heq
      | exact hp2 heq
      | exact hp2 heq.symm
      | exact hp0 heq
      | exact hp0 heq.symm
      | exact h02 heq
      | exact h02 heq.symm
      | exact hq₁0 heq
      | exact hq₂0 heq.symm
      | exact hq₁2 heq
      | exact hq₂2 heq.symm
      | exact a_index_ne_c2 data hq₁ heq
      | exact a_index_ne_c2 data hq₂ heq.symm
      | (subst heq; exact hne rfl)
      | (subst heq; simp at hr)
      | (simp at hr)
  by_cases hcp : core (data.cert.c p) ∈ t
  · -- `c_p` is blue to every `a` in `Z`
    have hna : ∀ q, a q ∈ t → False := by
      intro q hq
      have hpq : p ≠ q := by
        have := ((SimpleGraph.mem_commonNeighbors _).1 (hsub hq)).1
        simpa using this
      have hr := hred _ hq _ hcp (by simp)
      simp at hr
      rcases hr with h | ⟨-, h⟩
      · first
        | exact hpq h.symm
        | exact hpq (data.cert.c.injective h).symm
      · exact data.cert.c_ne_i _ _ h
    by_cases hz : z ∈ t
    · -- then `t ⊆ {c_p, z, w, b₁}` and `w b₁` is blue
      have hsub4 : t ⊆ {core (data.cert.c p), z, w} ∨ t ⊆ {core (data.cert.c p), z, b (c1Index data)} := by
        by_cases hw : w ∈ t
        · left
          intro u hu
          rcases hmem u hu with rfl | ⟨q, -, -, rfl⟩ | ⟨q, -, hq0, -, rfl⟩ | rfl | rfl | rfl
          · simp
          · exact (hna q hu).elim
          · exfalso
            have hr := hred _ hu _ hw (by simp)
            have hr' := hred _ hu _ hz (by simp)
            simp at hr hr'
            have h1 : q = c1Index data := Fin.ext (by
              have : q.val ≠ 0 := fun h ↦ hq0 (Fin.ext (by
                simp [SecondConnector.TypeA.c0Index, Certificates.c0Index, Certificates.indexZero, h]))
              simp [SecondConnector.TypeA.c1Index, Certificates.c1Index, Certificates.indexOne]
              omega)
            subst h1
            simp [SecondConnector.TypeA.c1Index,
              Certificates.c1Index, Certificates.indexOne] at hr
          · exfalso
            have hr := hred _ hu _ hz (by simp)
            simp [Switching.Vertex.i1] at hr
            exact i0_ne_i1 data hr
          · simp
          · simp
        · right
          intro u hu
          rcases hmem u hu with rfl | ⟨q, -, -, rfl⟩ | ⟨q, -, hq0, -, rfl⟩ | rfl | rfl | rfl
          · simp
          · exact (hna q hu).elim
          · have hr' := hred _ hu _ hz (by simp)
            simp at hr'
            have h1 : q = c1Index data := Fin.ext (by
              have : q.val ≠ 0 := fun h ↦ hq0 (Fin.ext (by
                simp [SecondConnector.TypeA.c0Index, Certificates.c0Index, Certificates.indexZero, h]))
              simp [SecondConnector.TypeA.c1Index, Certificates.c1Index, Certificates.indexOne]
              omega)
            subst h1
            simp
          · exfalso
            have hr := hred _ hu _ hz (by simp)
            simp [Switching.Vertex.i1] at hr
            exact i0_ne_i1 data hr
          · simp
          · exact absurd hu hw
      rcases hsub4 with h3 | h3 <;>
      · have hc := (Finset.card_le_card h3).trans Finset.card_le_three
        rw [ht.card_eq] at hc
        omega
    · have hmaps : Set.MapsTo (slotA data p) t (Finset.univ.erase (c0Index data)) := by
        intro u hu
        simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and]
        rcases hmem u hu with rfl | ⟨q, -, -, rfl⟩ | ⟨q, -, hq0, -, rfl⟩ | rfl | rfl | rfl
        · simpa using hp0
        · exact (hna q hu).elim
        · simpa using hq0
        · simpa using h02.symm
        · exact absurd hu hz
        · simpa using h02.symm
      have hc := Finset.card_le_card_of_injOn (slotA data p) hmaps hinj
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        ht.card_eq] at hc
      omega
  · have hmaps : Set.MapsTo (slotA data p) t (Finset.univ.erase p) := by
      intro u hu
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and]
      rcases hmem u hu with rfl | ⟨q, hqp, -, rfl⟩ | ⟨q, hqp, -, -, rfl⟩ | rfl | rfl | rfl
      · exact absurd hu hcp
      · simpa using hqp
      · simpa using hqp
      · simpa using Ne.symm hp2
      · simpa using Ne.symm hp0
      · simpa using Ne.symm hp2
    have hc := Finset.card_le_card_of_injOn (slotA data p) hmaps hinj
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      ht.card_eq] at hc
    omega

end

end ThirdConnector
end RamseyIncrement
