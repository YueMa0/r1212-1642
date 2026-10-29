/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Basic

/-!
# Adjoining a vertex with a prescribed red neighborhood

This file supplies the generic final step used by the second-connector
construction.  An old graph `H` is extended by one vertex `w`; the predicate
`redToW` specifies exactly the old vertices joined to `w` in red.
-/

namespace RamseyIncrement
namespace SecondConnector

open SimpleGraph

universe u

variable {V : Type u} {H : SimpleGraph V} {k s : ℕ}

/-- The old vertices together with the second connector. -/
abbrev AdjoinVertex (V : Type*) := V ⊕ Unit

namespace AdjoinVertex

/-- Inclusion of an old vertex. -/
abbrev old (v : V) : AdjoinVertex V := Sum.inl v

/-- The newly adjoined vertex. -/
abbrev w : AdjoinVertex V := Sum.inr ()

end AdjoinVertex

/-- Adjoin one vertex whose red neighborhood among the old vertices is
specified by `redToW`. -/
def adjoinWithRedNeighborhood
    (H : SimpleGraph V) (redToW : V → Prop) :
    SimpleGraph (AdjoinVertex V) where
  Adj
    | .inl u, .inl v => H.Adj u v
    | .inl u, .inr _ => redToW u
    | .inr _, .inl v => redToW v
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro u v
    cases u <;> cases v <;> simp only
    · exact H.adj_symm
    · exact id
    · exact id
    · exact id
  loopless := by
    constructor
    intro v
    cases v with
    | inl v => exact H.loopless.irrefl v
    | inr _ => exact id

namespace adjoinWithRedNeighborhood

variable (H : SimpleGraph V) (redToW : V → Prop)

@[simp]
theorem adj_old_old (u v : V) :
    (adjoinWithRedNeighborhood H redToW).Adj
      (AdjoinVertex.old u) (AdjoinVertex.old v) ↔ H.Adj u v :=
  Iff.rfl

@[simp]
theorem adj_old_w (u : V) :
    (adjoinWithRedNeighborhood H redToW).Adj
      (AdjoinVertex.old u) AdjoinVertex.w ↔ redToW u :=
  Iff.rfl

@[simp]
theorem adj_w_old (u : V) :
    (adjoinWithRedNeighborhood H redToW).Adj
      AdjoinVertex.w (AdjoinVertex.old u) ↔ redToW u :=
  Iff.rfl

@[simp]
theorem not_adj_w_w :
    ¬(adjoinWithRedNeighborhood H redToW).Adj
      AdjoinVertex.w AdjoinVertex.w :=
  id

@[simp]
theorem compl_adj_old_old (u v : V) :
    (adjoinWithRedNeighborhood H redToW)ᶜ.Adj
      (AdjoinVertex.old u) (AdjoinVertex.old v) ↔ Hᶜ.Adj u v := by
  simp [SimpleGraph.compl_adj]

@[simp]
theorem compl_adj_old_w (u : V) :
    (adjoinWithRedNeighborhood H redToW)ᶜ.Adj
      (AdjoinVertex.old u) AdjoinVertex.w ↔ ¬redToW u := by
  simp [SimpleGraph.compl_adj]

@[simp]
theorem compl_adj_w_old (u : V) :
    (adjoinWithRedNeighborhood H redToW)ᶜ.Adj
      AdjoinVertex.w (AdjoinVertex.old u) ↔ ¬redToW u := by
  simp [SimpleGraph.compl_adj]

end adjoinWithRedNeighborhood

namespace AdjoinProof

/-- Old vertices of a finite set in the adjoined vertex type. -/
private abbrev OldIn (K : Finset (AdjoinVertex V)) :=
  {v : V // AdjoinVertex.old v ∈ K}

/-- New-vertex tags of a finite set in the adjoined vertex type. -/
private abbrev NewIn (K : Finset (AdjoinVertex V)) :=
  {z : Unit // Sum.inr z ∈ K}

private instance oldInFinite (K : Finset (AdjoinVertex V)) :
    Finite (OldIn K) :=
  Finite.of_injective
    (fun v : OldIn K =>
      (⟨AdjoinVertex.old v.1, v.2⟩ : {x // x ∈ K}))
    (by
      intro v u h
      apply Subtype.ext
      exact Sum.inl.inj (congrArg Subtype.val h))

private noncomputable instance oldInFintype
    (K : Finset (AdjoinVertex V)) : Fintype (OldIn K) :=
  Fintype.ofFinite _

private noncomputable instance newInFintype
    (K : Finset (AdjoinVertex V)) : Fintype (NewIn K) :=
  Fintype.ofFinite _

/-- Partition a finite set into its old part and its possible new vertex. -/
private def setEquiv (K : Finset (AdjoinVertex V)) :
    {x // x ∈ K} ≃ OldIn K ⊕ NewIn K where
  toFun x :=
    match x.1, x.2 with
    | .inl v, hv => Sum.inl ⟨v, hv⟩
    | .inr z, hz => Sum.inr ⟨z, hz⟩
  invFun
    | Sum.inl v => ⟨AdjoinVertex.old v.1, v.2⟩
    | Sum.inr z => ⟨Sum.inr z.1, z.2⟩
  left_inv x := by rcases x with ⟨x, hx⟩; cases x <;> rfl
  right_inv x := by rcases x with (v | z) <;> rfl

private theorem card_decompose (K : Finset (AdjoinVertex V)) :
    K.card = Fintype.card (OldIn K) + Fintype.card (NewIn K) := by
  classical
  rw [← Fintype.card_coe K, Fintype.card_congr (setEquiv K)]
  simp

/-- A clique-free-on hypothesis gives a cardinal bound for any finite
family embedded into the specified set. -/
private theorem card_lt_of_cliqueFreeOn_of_embedding
    {W : Type*} [Fintype W] {G : SimpleGraph V} {S : Set V} {n : ℕ}
    (hfree : G.CliqueFreeOn S n)
    (f : W ↪ V)
    (hmem : ∀ x : W, f x ∈ S)
    (hclique : ∀ x y : W, x ≠ y → G.Adj (f x) (f y)) :
    Fintype.card W < n := by
  classical
  by_contra hnot
  have hn : n ≤ Fintype.card W := Nat.le_of_not_gt hnot
  obtain ⟨t, -, htcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset W)) hn
  let image : Finset V := t.map f
  apply hfree (by
    intro v hv
    change v ∈ image at hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hv
    exact hmem x)
  refine ⟨?_, by simp [image, htcard]⟩
  intro v hv u hu hvu
  change v ∈ image at hv
  change u ∈ image at hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hv
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hu
  exact hclique x y (fun hxy => hvu (congrArg f hxy))

/-- Old vertices belonging to a clique in the adjoined graph form a clique
in the old graph. -/
private theorem oldIn_clique
    (redToW : V → Prop)
    {K : Finset (AdjoinVertex V)}
    (hK : (adjoinWithRedNeighborhood H redToW).IsClique K)
    (u v : OldIn K) (huv : u ≠ v) :
    H.Adj u.1 v.1 := by
  rw [← adjoinWithRedNeighborhood.adj_old_old H redToW]
  exact hK u.2 v.2 (by
    intro h
    apply huv
    apply Subtype.ext
    exact Sum.inl.inj h)

/-- Blue analogue of `oldIn_clique`. -/
private theorem oldIn_compl_clique
    (redToW : V → Prop)
    {K : Finset (AdjoinVertex V)}
    (hK : (adjoinWithRedNeighborhood H redToW)ᶜ.IsClique K)
    (u v : OldIn K) (huv : u ≠ v) :
    Hᶜ.Adj u.1 v.1 := by
  rw [← adjoinWithRedNeighborhood.compl_adj_old_old H redToW]
  exact hK u.2 v.2 (by
    intro h
    apply huv
    apply Subtype.ext
    exact Sum.inl.inj h)

/-- There is at most one new-vertex tag in a finite set. -/
private theorem card_newIn_le_one (K : Finset (AdjoinVertex V)) :
    Fintype.card (NewIn K) ≤ 1 := by
  let f : NewIn K ↪ Unit :=
    ⟨Subtype.val, Subtype.val_injective⟩
  simpa using Fintype.card_le_of_injective f f.injective

/-- If the distinguished new vertex is absent, the new part has cardinality
zero. -/
private theorem card_newIn_eq_zero_of_not_mem
    (K : Finset (AdjoinVertex V)) (hw : AdjoinVertex.w ∉ K) :
    Fintype.card (NewIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro z
  exact hw (by simpa [AdjoinVertex.w] using z.2)

end AdjoinProof

/-- A one-vertex extension is Ramsey-free when the old graph is Ramsey-free
and the two color neighborhoods of the new vertex exclude the corresponding
one-smaller cliques. -/
theorem adjoin_isRamseyFree
    {redToW : V → Prop}
    (hH : IsRamseyFree H (k + 1) (s + 1))
    (hred : H.CliqueFreeOn {v | redToW v} k)
    (hblue : Hᶜ.CliqueFreeOn {v | ¬redToW v} s) :
    IsRamseyFree (adjoinWithRedNeighborhood H redToW)
      (k + 1) (s + 1) := by
  classical
  constructor
  · intro K hK
    let oldEmbedding : AdjoinProof.OldIn K ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hparts := AdjoinProof.card_decompose K
    have hnewLe := AdjoinProof.card_newIn_le_one K
    by_cases hw : AdjoinVertex.w ∈ K
    · have holdMem :
          ∀ v : AdjoinProof.OldIn K, oldEmbedding v ∈ {v | redToW v} := by
        intro v
        change redToW v.1
        rw [← adjoinWithRedNeighborhood.adj_old_w H redToW]
        exact hK.isClique v.2 hw (by simp)
      have holdLt : Fintype.card (AdjoinProof.OldIn K) < k :=
        AdjoinProof.card_lt_of_cliqueFreeOn_of_embedding
          hred oldEmbedding holdMem
          (AdjoinProof.oldIn_clique redToW hK.isClique)
      have hcard := hK.card_eq
      omega
    · have hnewZero :=
        AdjoinProof.card_newIn_eq_zero_of_not_mem K hw
      have holdLt : Fintype.card (AdjoinProof.OldIn K) < k + 1 :=
        AdjoinProof.card_lt_of_cliqueFreeOn_of_embedding
          hH.1.cliqueFreeOn oldEmbedding (fun _ => Set.mem_univ _)
          (AdjoinProof.oldIn_clique redToW hK.isClique)
      have hcard := hK.card_eq
      omega
  · intro K hK
    let oldEmbedding : AdjoinProof.OldIn K ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hparts := AdjoinProof.card_decompose K
    have hnewLe := AdjoinProof.card_newIn_le_one K
    by_cases hw : AdjoinVertex.w ∈ K
    · have holdMem :
          ∀ v : AdjoinProof.OldIn K,
            oldEmbedding v ∈ {v | ¬redToW v} := by
        intro v
        change ¬redToW v.1
        rw [← adjoinWithRedNeighborhood.compl_adj_old_w H redToW]
        exact hK.isClique v.2 hw (by simp)
      have holdLt : Fintype.card (AdjoinProof.OldIn K) < s :=
        AdjoinProof.card_lt_of_cliqueFreeOn_of_embedding
          hblue oldEmbedding holdMem
          (AdjoinProof.oldIn_compl_clique redToW hK.isClique)
      have hcard := hK.card_eq
      omega
    · have hnewZero :=
        AdjoinProof.card_newIn_eq_zero_of_not_mem K hw
      have holdLt : Fintype.card (AdjoinProof.OldIn K) < s + 1 :=
        AdjoinProof.card_lt_of_cliqueFreeOn_of_embedding
          hH.2.cliqueFreeOn oldEmbedding (fun _ => Set.mem_univ _)
          (AdjoinProof.oldIn_compl_clique redToW hK.isClique)
      have hcard := hK.card_eq
      omega

@[simp]
theorem card_adjoinVertex [Fintype V] :
    Fintype.card (AdjoinVertex V) = Fintype.card V + 1 := by
  simp [AdjoinVertex]

end SecondConnector
end RamseyIncrement
