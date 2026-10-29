/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.Projection
import RamseyIncrement.SecondConnector.TypeA.ChangedEdges

/-!
# Type A red cliques through the second connector

This file formalizes the Type A red-neighborhood analysis from the
strengthened second-connector argument.  The first group of lemmas handles
the three possible `Y`-vertices.  In particular, the `y₀` and `y₂` arguments retain the
possible vertex `a₀` and discharge that subcase by the explicit
`3 + |Q|` count.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeA

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private abbrev c0
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.c (c0Index data)

private abbrev i0
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.i (i0Index data)

private abbrev i2
    (data : Certificates.PlusCaseAData G k s) : V :=
  data.cert.i (i2Index data)

private abbrev a0
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c0Index data)

private abbrev xStar
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

private abbrev y0
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert (some (i0Index data))

private abbrev y2
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert (some (i2Index data))

private abbrev yStar
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.y data.cert none

private abbrev zVertex : Switching.Vertex V k s :=
  Switching.Vertex.z

private theorem i0_ne_i2
    (data : Certificates.PlusCaseAData G k s) :
    i0Index data ≠ i2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [i0Index, i2Index, Certificates.i0Index',
    Certificates.i2Index'] at hval

private theorem c0_ne_c2
    (data : Certificates.PlusCaseAData G k s) :
    c0Index data ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c0Index, c2Index, Certificates.c0Index,
    Certificates.c2Index] at hval

private theorem card_index_away_from_two
    (data : Certificates.PlusCaseAData G k s) :
    Fintype.card
      {p : Fin (k - 1) // p ≠ c2Index data} = k - 2 := by
  classical
  have hone :
      Fintype.card
        {p : Fin (k - 1) // p = c2Index data} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨c2Index data, rfl⟩, by
      rintro ⟨p, hp⟩
      exact Subtype.ext hp⟩
  rw [Fintype.card_subtype_compl
    (fun p : Fin (k - 1) => p = c2Index data)]
  simp only [Fintype.card_fin, hone]
  have hk := data.cert.five_le_k
  omega

private theorem card_index_away_from_zero_two
    (data : Certificates.PlusCaseAData G k s) :
    Fintype.card
      {p : Fin (k - 1) //
        ¬(p = c0Index data ∨ p = c2Index data)} = k - 3 := by
  classical
  let e :
      {p : Fin (k - 1) //
        p = c0Index data ∨ p = c2Index data} ≃ Bool :=
    { toFun := fun p =>
        if p.1 = c0Index data then false else true
      invFun := fun b =>
        if b then
          ⟨c2Index data, Or.inr rfl⟩
        else
          ⟨c0Index data, Or.inl rfl⟩
      left_inv := by
        rintro ⟨p, hp⟩
        apply Subtype.ext
        rcases hp with hp | hp
        · subst p
          simp
        · subst p
          simp [(c0_ne_c2 data).symm]
      right_inv := by
        intro b
        cases b <;> simp [(c0_ne_c2 data).symm] }
  have htwo :
      Fintype.card
        {p : Fin (k - 1) //
          p = c0Index data ∨ p = c2Index data} = 2 := by
    calc
      _ = Fintype.card Bool := Fintype.card_congr e
      _ = 2 := Fintype.card_bool
  rw [Fintype.card_subtype_compl
    (fun p : Fin (k - 1) =>
      p = c0Index data ∨ p = c2Index data)]
  simp only [Fintype.card_fin, htwo]
  have hk := data.cert.five_le_k
  omega

/-! ## Neighborhood and adjacency classifiers -/

/-- The block form of the red neighborhood displayed in (21A). -/
private theorem red_member_cases
    (data : Certificates.PlusCaseAData G k s)
    {v : Switching.Vertex V k s}
    (hv : redToWA data v) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ((∃ p, d = data.cert.c p) ∨ G.Adj (i0 data) d)) ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.a p ∧ p ≠ c2Index data) ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.b p ∧ p ∈ Q data) ∨
    v = xStar data ∨
    v = y0 data ∨
    v = y2 data ∨
    v = yStar data ∨
    v = zVertex := by
  rcases vertex_six_block_cases data.cert v with
      h | h | h | h | h | h
  · obtain ⟨d, rfl⟩ := h
    exact Or.inl ⟨d, rfl, (redToWA_core data d).1 hv⟩
  · obtain ⟨p, rfl⟩ := h
    exact Or.inr (Or.inl
      ⟨p, rfl, (redToWA_a data p).1 hv⟩)
  · obtain ⟨p, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl
      ⟨p, rfl, (redToWA_b data p).1 hv⟩))
  · obtain ⟨r, rfl⟩ := h
    have hr := (redToWA_x data r).1 hv
    subst r
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · obtain ⟨r, rfl⟩ := h
    rcases (redToWA_y data r).1 hv with hr | hr | hr
    · subst r
      exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · subst r
      exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl))))
    · subst r
      exact Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl)))))
  · subst v
    exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-- The only red edge created by (14A) meets `a₂`, which is blue to `w`.
Consequently every edge of a red clique in `N_R(w)` was already red in
the first-connector graph. -/
private theorem old_adj_implies_final
    (data : Certificates.PlusCaseAData G k s)
    {u v : Switching.Vertex V k s}
    (hu : redToWA data u) (hv : redToWA data v)
    (huv : (extraAOldGraph data).Adj u v) :
    (Switching.finalGraph data.cert).Adj u v := by
  by_contra hfinal
  have hnew := classify_extraA_new_red_edge data huv hfinal
  rcases hnew with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact ((redToWA_a data (c2Index data)).1 hv) rfl
  · rcases h with ⟨rfl, rfl⟩
    exact ((redToWA_a data (c2Index data)).1 hu) rfl

private theorem final_adj_core_core_iff
    (data : Certificates.PlusCaseAData G k s) (u v : V) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core u) (Switching.Vertex.core v) ↔
        G.Adj u v := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core]
  constructor
  · rintro ⟨hne, hadj⟩
    exact hadj hne
  · intro hadj
    exact ⟨hadj.ne, fun _ ↦ hadj⟩

private theorem final_adj_core_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.b p) ↔
        v ≠ data.cert.c p ∧ G.Adj (data.cert.c p) v := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core, Switching.Vertex.b]

private theorem final_adj_core_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (q : Fin (s - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v)
      (Switching.Vertex.y data.cert (some q)) ↔
        v = data.cert.i q ∨ G.Adj (data.cert.i q) v := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_adj_b_y_iff_of_ne_c0
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) (q : Fin (s - 1))
    (hp0 : p ≠ c0Index data) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.b p)
      (Switching.Vertex.y data.cert (some q)) ↔
        G.Adj (data.cert.c p) (data.cert.i q) := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, hp0]
  intro _ hEq
  exact data.cert.c_ne_i p q hEq.symm

private theorem final_adj_z_core_iff
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.core v) ↔
        v ≠ c0 data ∧ G.Adj (c0 data) v := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.core, Switching.Vertex.b, zVertex, c0]

private theorem final_adj_z_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.b p) ↔
        p = c0Index data ∨
          (c0Index data ≠ p ∧
            SameBPart (c0Index data) p) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.b, zVertex, c0Index]
  aesop

private theorem final_adj_z_y_iff
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    (Switching.finalGraph data.cert).Adj zVertex
      (Switching.Vertex.y data.cert (some q)) ↔ q ∈ data.cert.T := by
  have hpre :
      (Switching.preGraph data.cert).Adj zVertex
          (Switching.Vertex.y data.cert (some q)) ↔
        q ∈ data.cert.T := by
    change
      (Switching.redJoinedClone (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.b ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              data.cert.five_le_s)).symm (some q)))) ↔
        q ∈ data.cert.T
    rw [Switching.redJoinedClone.adj_z_old]
    rw [or_iff_right (by simp)]
    exact Switching.preGraph_adj_b0_y_iff data.cert q
  rw [Switching.final_adj_iff, hpre]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_not_adj_y_a_of_ne_c0
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1))
    (hp0 : p ≠ c0Index data) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.y data.cert (some q))
      (Switching.Vertex.a p) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, hp0]
  exact data.cert.c_ne_i p q

private theorem final_not_adj_ySome_xStar
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.y data.cert (some q)) (xStar data) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_x_y_iff,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, xStar]

private theorem final_not_adj_z_a0
    (data : Certificates.PlusCaseAData G k s) :
    ¬(Switching.finalGraph data.cert).Adj zVertex (a0 data) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b, zVertex, a0]

private theorem final_not_adj_y2_yStar
    (data : Certificates.PlusCaseAData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (y2 data) (yStar data) := by
  have hs : 2 < s := by
    have := data.cert.five_le_s
    omega
  have hpre :
      ¬(Switching.preGraph data.cert).Adj
        (y2 data) (yStar data) := by
    rw [Switching.preGraph_adj_y_y_iff]
    simp [Canonical.outerIndexEquiv, SameBPart, i2Index]
    omega
  rw [Switching.final_adj_iff]
  simp [hpre, Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, y2, yStar]

private theorem final_adj_yStar_core_iff
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    (Switching.finalGraph data.cert).Adj
      (yStar data) (Switching.Vertex.core v) ↔
        v = c0 data := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_y_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, yStar, c0]
  exact eq_comm

private theorem final_not_adj_yStar_z
    (data : Certificates.PlusCaseAData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (yStar data) zVertex := by
  have hpre :
      ¬(Switching.preGraph data.cert).Adj
        zVertex (yStar data) := by
    change
      ¬(Switching.redJoinedClone
        (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.b ((Canonical.outerIndexEquiv
            (le_trans (by decide : 1 ≤ 5)
              data.cert.five_le_s)).symm none)))
    rw [Switching.redJoinedClone.adj_z_old]
    push Not
    constructor
    · simp
    · exact Switching.preGraph_not_adj_b0_yStar data.cert
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [hpre, Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, yStar]

private theorem final_not_adj_a_b_same
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    ¬(Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.b p) := by
  rw [Switching.final_adj_iff]
  simp [Switching.preGraph,
    Switching.canonicalGraph, Canonical.graph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.Vertex.a, Switching.Vertex.b]

private theorem final_adj_core_a_iff
    (data : Certificates.PlusCaseAData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.a p) ↔
        data.cert.c p = v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_adj_a_a_iff
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.a q) ↔ p ≠ q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_adj_a_b_iff
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.a p) (Switching.Vertex.b q) ↔ p ≠ q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]

private theorem final_not_adj_xStar_a0
    (data : Certificates.PlusCaseAData G k s) :
    ¬(Switching.finalGraph data.cert).Adj
      (xStar data) (a0 data) := by
  rw [(Switching.finalGraph data.cert).adj_comm,
    Switching.final_adj_iff]
  simp [Switching.preGraph_adj_lower_x_iff,
    Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, xStar, a0]

private theorem Q_ne_c0
    (data : Certificates.PlusCaseAData G k s)
    {p : Fin (k - 1)} (hp : p ∈ Q data) :
    p ≠ c0Index data := by
  have hp2 := (mem_Q data p).1 hp |>.1
  intro h
  subst p
  simp [c0Index, Certificates.c0Index] at hp2

private theorem Q_ne_c2
    (data : Certificates.PlusCaseAData G k s)
    {p : Fin (k - 1)} (hp : p ∈ Q data) :
    p ≠ c2Index data :=
  fun h ↦ ((mem_Q data p).1 hp).2 (h ▸ c2_mem_P data)

private theorem final_adj_b_b_iff_of_mem_Q
    (data : Certificates.PlusCaseAData G k s)
    (p q : Fin (k - 1))
    (hp : p ∈ Q data) (hq : q ∈ Q data) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.b p) (Switching.Vertex.b q) ↔
        p ≠ q ∧ SameBPart p q := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_b_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair, Q_ne_c0 data hp, Q_ne_c0 data hq,
    Q_ne_c2 data hp, Q_ne_c2 data hq]

private theorem not_old_adj_z_b_of_mem_Q
    (data : Certificates.PlusCaseAData G k s)
    {p : Fin (k - 1)} (hp : p ∈ Q data) :
    ¬(extraAOldGraph data).Adj zVertex
      (Switching.Vertex.b p) := by
  intro h
  have hf := old_adj_implies_final data
    (redToWA_z data) ((redToWA_b data p).2 hp) h
  have hz := (final_adj_z_b_iff data p).1 hf
  rcases hz with hp0 | hp0
  · exact Q_ne_c0 data hp hp0
  · rcases hp0.2 with hsmall | hlarge
    · have hp2 := ((mem_Q data p).1 hp).1
      omega
    · have h0 := hlarge.1
      simp [c0Index, Certificates.c0Index] at h0

/-- In a red clique containing `y_q`, with `q=0` or `q=2`, and no
`a₀`, every vertex is core, a `B_Q` vertex, `y_q`, or `z`. -/
private theorem member_cases_y_no_a0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {q : Fin (s - 1)}
    (hq : q = i0Index data ∨ q = i2Index data)
    (hy : Switching.Vertex.y data.cert (some q) ∈ K)
    (ha0 : a0 data ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p ∈ Q data, v = Switching.Vertex.b p) ∨
    v = Switching.Vertex.y data.cert (some q) ∨
    v = zVertex := by
  have hvred : redToWA data v := hKS hv
  have hyred : redToWA data
      (Switching.Vertex.y data.cert (some q)) := hKS hy
  rcases red_member_cases data hvred with
      hcore | ha | hb | hx | hy0' | hy2' | hys | hz
  · obtain ⟨d, hd, _⟩ := hcore
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨p, rfl, hp2⟩ := ha
    by_cases hp0 : p = c0Index data
    · subst p
      exact False.elim (ha0 hv)
    · have hfinal :=
        old_adj_implies_final data hyred hvred
          (hK hy hv (by simp))
      exact False.elim
        (final_not_adj_y_a_of_ne_c0 data q p hp0 hfinal)
  · obtain ⟨p, rfl, hpQ⟩ := hb
    exact Or.inr (Or.inl ⟨p, hpQ, rfl⟩)
  · subst v
    have hfinal :=
      old_adj_implies_final data hyred hvred
        (hK hy hv (by simp [xStar]))
    exact False.elim (final_not_adj_ySome_xStar data q hfinal)
  · subst v
    rcases hq with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · have hrem :
          (extraARemovedRedGraph data).Adj (y0 data) (y2 data) := by
        rw [extraARemovedRedGraph_adj_iff]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact False.elim
        (extraAOldGraph_not_adj_of_removed data hrem
          ((extraAOldGraph data).adj_symm
            (hK hy hv (by
              simpa [y0, y2] using (i0_ne_i2 data).symm))))
  · subst v
    rcases hq with rfl | rfl
    · have hrem :
          (extraARemovedRedGraph data).Adj (y0 data) (y2 data) := by
        rw [extraARemovedRedGraph_adj_iff]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact False.elim
        (extraAOldGraph_not_adj_of_removed data hrem
          (hK hy hv (by
            simpa [y0, y2] using i0_ne_i2 data)))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · subst v
    rcases hq with rfl | rfl
    · have hrem :
          (extraARemovedRedGraph data).Adj (y0 data) (yStar data) := by
        rw [extraARemovedRedGraph_adj_iff]
        exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
      exact False.elim
        (extraAOldGraph_not_adj_of_removed data hrem
          (hK hy hv (by simp [yStar])))
    · have hfinal :=
        old_adj_implies_final data hyred hvred
          (hK hy hv (by simp [yStar]))
      exact False.elim (final_not_adj_y2_yStar data hfinal)
  · exact Or.inr (Or.inr (Or.inr hz))

/-! ## The `y₀` and `y₂` projection cases -/

/-- Projection used for `y₀` and `y₂`: `y_q ↦ i_q`, `b_p ↦ c_p`,
`z ↦ c₀`, and core vertices are retained. -/
private def yProjection
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    Switching.Vertex V k s → V
  | .inl (.core (.core v)) => v
  | .inl (.core (.b p)) => data.cert.c p
  | .inl (.b _) => data.cert.i q
  | .inr _ => c0 data
  | _ => c0 data

@[simp]
private theorem yProjection_core
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (v : V) :
    yProjection data q (Switching.Vertex.core v) = v :=
  rfl

@[simp]
private theorem yProjection_b
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    yProjection data q (Switching.Vertex.b p) = data.cert.c p :=
  rfl

@[simp]
private theorem yProjection_y
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    yProjection data q
      (Switching.Vertex.y data.cert (some q)) = data.cert.i q := by
  simp [yProjection]

@[simp]
private theorem yProjection_z
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    yProjection data q zVertex = c0 data :=
  rfl

private theorem cert_i_not_red
    (data : Certificates.PlusCaseAData G k s)
    (q r : Fin (s - 1)) :
    ¬G.Adj (data.cert.i q) (data.cert.i r) := by
  by_cases hqr : q = r
  · subst r
    exact G.loopless.irrefl _
  · exact ((SimpleGraph.compl_adj _ _ _).1
      (data.cert.i_compl_adj hqr)).2

private theorem not_redToWA_core_i
    (data : Certificates.PlusCaseAData G k s)
    (q : Fin (s - 1)) :
    ¬redToWA data
      (Switching.Vertex.core (data.cert.i q)) := by
  rw [redToWA_core]
  rintro (⟨p, hp⟩ | hred)
  · exact data.cert.c_ne_i p q hp.symm
  · exact cert_i_not_red data (i0Index data) q hred

private theorem yProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {q : Fin (s - 1)}
    (hq : q = i0Index data ∨ q = i2Index data)
    (hy : Switching.Vertex.y data.cert (some q) ∈ K)
    (ha0 : a0 data ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data).Adj u v) :
    G.Adj (yProjection data q u) (yProjection data q v) := by
  have hured : redToWA data u := hKS hu
  have hvred : redToWA data v := hKS hv
  have hufinal := old_adj_implies_final data hured hvred huv
  rcases member_cases_y_no_a0 data hKS hK hq hy ha0 hu with
      ⟨d, rfl⟩ | ⟨p, hpQ, rfl⟩ | rfl | rfl <;>
    rcases member_cases_y_no_a0 data hKS hK hq hy ha0 hv with
      ⟨e, rfl⟩ | ⟨r, hrQ, rfl⟩ | rfl | rfl
  · simpa using (final_adj_core_core_iff data d e).1 hufinal
  · simpa using ((final_adj_core_b_iff data d r).1 hufinal).2.symm
  · rcases (final_adj_core_y_iff data d q).1 hufinal with h | h
    · subst d
      exact False.elim (not_redToWA_core_i data q hured)
    · simpa using h.symm
  · simpa using
      ((final_adj_z_core_iff data d).1
        ((Switching.finalGraph data.cert).adj_symm hufinal)).2.symm
  · simpa using
      ((final_adj_core_b_iff data e p).1
        ((Switching.finalGraph data.cert).adj_symm hufinal)).2
  · simpa using data.cert.c_adj
      (fun hpr ↦ huv.ne (congrArg Switching.Vertex.b hpr))
  · simpa using (final_adj_b_y_iff_of_ne_c0 data p q
      (Q_ne_c0 data hpQ)).1 hufinal
  · exact False.elim
      (not_old_adj_z_b_of_mem_Q data hpQ
        ((extraAOldGraph data).adj_symm huv))
  · rcases (final_adj_core_y_iff data e q).1
      ((Switching.finalGraph data.cert).adj_symm hufinal) with h | h
    · subst e
      exact False.elim (not_redToWA_core_i data q hvred)
    · simpa using h
  · simpa using ((final_adj_b_y_iff_of_ne_c0 data r q
      (Q_ne_c0 data hrQ)).1
        ((Switching.finalGraph data.cert).adj_symm hufinal)).symm
  · exact False.elim (huv.ne rfl)
  · have hT := (final_adj_z_y_iff data q).1
      ((Switching.finalGraph data.cert).adj_symm hufinal)
    simpa using ((data.cert.mem_T q).1 hT).symm
  · simpa using ((final_adj_z_core_iff data e).1 hufinal).2
  · exact False.elim
      (not_old_adj_z_b_of_mem_Q data hrQ huv)
  · have hT := (final_adj_z_y_iff data q).1 hufinal
    simpa using (data.cert.mem_T q).1 hT
  · exact False.elim (huv.ne rfl)

private theorem card_lt_of_y_no_a0
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {q : Fin (s - 1)}
    (hq : q = i0Index data ∨ q = i2Index data)
    (hy : Switching.Vertex.y data.cert (some q) ∈ K)
    (ha0 : a0 data ∉ K) :
    K.card < k := by
  let f := yProjection data q
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data).Adj u v → G.Adj (f u) (f v) :=
    fun {_ _} hu hv huv ↦
      yProjection_maps_adj data hKS hK hq hy ha0 hu hv huv
  have hinj : Set.InjOn f (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ ↦ Set.mem_univ _)
    hadj hG.1.cliqueFreeOn hK

/-- The finite set of red `B`-vertices indexed by `Q`. -/
private noncomputable def bQSet
    (data : Certificates.PlusCaseAData G k s) :
    Finset (Switching.Vertex V k s) :=
  (Q data).map
    ⟨Switching.Vertex.b, vertex_b_injective⟩

@[simp]
private theorem mem_bQSet
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    Switching.Vertex.b p ∈ bQSet data ↔ p ∈ Q data := by
  simp [bQSet]

@[simp]
private theorem card_bQSet
    (data : Certificates.PlusCaseAData G k s) :
    (bQSet data).card = (Q data).card := by
  simp [bQSet]

/-- The explicit `a₀` subcase in both the `y₀` and `y₂` rows:
only `y_q,a₀,c₀`, and the `B_Q` clique remain. -/
private theorem card_lt_of_y_with_a0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {q : Fin (s - 1)}
    (hq : q = i0Index data ∨ q = i2Index data)
    (hy : Switching.Vertex.y data.cert (some q) ∈ K)
    (ha0 : a0 data ∈ K) :
    K.card < k := by
  classical
  have hyred : redToWA data
      (Switching.Vertex.y data.cert (some q)) := hKS hy
  have ha0red : redToWA data (a0 data) := hKS ha0
  have hsub :
      K ⊆ insert (Switching.Vertex.y data.cert (some q))
        (insert (a0 data)
          (insert (Switching.Vertex.core (c0 data)) (bQSet data))) := by
    intro v hv
    have hvred : redToWA data v := hKS hv
    rcases red_member_cases data hvred with
        hcore | ha | hb | hx | hy0' | hy2' | hys | hz
    · obtain ⟨d, rfl, _⟩ := hcore
      by_cases hd : d = c0 data
      · subst d
        simp
      · have hfinal :=
          old_adj_implies_final data ha0red hvred
            (hK ha0 hv (by simp))
        have haCore :
            (Switching.finalGraph data.cert).Adj
              (a0 data) (Switching.Vertex.core d) := hfinal
        rw [Switching.final_adj_iff] at haCore
        simp [Switching.preGraph_adj_lower_lower_iff,
          Switching.removedRedGraph_adj_iff,
          Switching.addedRedGraph_adj_iff,
          Switching.SymmPair, a0] at haCore
        exact False.elim (hd haCore.symm)
    · obtain ⟨p, rfl, hp2⟩ := ha
      have hp0 : p = c0Index data := by
        by_contra hp0
        have hfinal :=
          old_adj_implies_final data hyred hvred
            (hK hy hv (by simp))
        exact final_not_adj_y_a_of_ne_c0 data q p hp0 hfinal
      subst p
      simp
    · obtain ⟨p, rfl, hpQ⟩ := hb
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem ((mem_bQSet data p).2 hpQ)))
    · subst v
      have hfinal :=
        old_adj_implies_final data hyred hvred
          (hK hy hv (by simp [xStar]))
      exact False.elim (final_not_adj_ySome_xStar data q hfinal)
    · subst v
      rcases hq with rfl | rfl
      · simp
      · have hrem :
            (extraARemovedRedGraph data).Adj (y0 data) (y2 data) := by
          rw [extraARemovedRedGraph_adj_iff]
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        exact False.elim
          (extraAOldGraph_not_adj_of_removed data hrem
            ((extraAOldGraph data).adj_symm
              (hK hy hv (by
                simpa [y0, y2] using (i0_ne_i2 data).symm))))
    · subst v
      rcases hq with rfl | rfl
      · have hrem :
            (extraARemovedRedGraph data).Adj (y0 data) (y2 data) := by
          rw [extraARemovedRedGraph_adj_iff]
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        exact False.elim
          (extraAOldGraph_not_adj_of_removed data hrem
            (hK hy hv (by
              simpa [y0, y2] using i0_ne_i2 data)))
      · simp
    · subst v
      rcases hq with rfl | rfl
      · have hrem :
            (extraARemovedRedGraph data).Adj (y0 data) (yStar data) := by
          rw [extraARemovedRedGraph_adj_iff]
          exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
        exact False.elim
          (extraAOldGraph_not_adj_of_removed data hrem
            (hK hy hv (by simp [yStar])))
      · have hfinal :=
          old_adj_implies_final data hyred hvred
            (hK hy hv (by simp [yStar]))
        exact False.elim (final_not_adj_y2_yStar data hfinal)
    · subst v
      have hfinal :=
        old_adj_implies_final data ha0red hvred
          (hK ha0 hv (by simp))
      exact False.elim (final_not_adj_z_a0 data
        ((Switching.finalGraph data.cert).adj_symm hfinal))
  have hcard := Finset.card_le_card hsub
  have h1 := Finset.card_insert_le
    (Switching.Vertex.y data.cert (some q))
    (insert (a0 data)
      (insert (Switching.Vertex.core (c0 data)) (bQSet data)))
  have h2 := Finset.card_insert_le
    (a0 data) (insert (Switching.Vertex.core (c0 data)) (bQSet data))
  have h3 := Finset.card_insert_le
    (Switching.Vertex.core (c0 data)) (bQSet data)
  rw [card_bQSet] at h3
  have hQ := card_Q_le data
  have hk := data.cert.five_le_k
  omega

/-- Complete `y₀` row, including the possible `a₀`. -/
theorem red_clique_card_lt_of_y0
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∈ K) :
    K.card < k := by
  by_cases ha0 : a0 data ∈ K
  · exact card_lt_of_y_with_a0 data hKS hK
      (Or.inl rfl) hy0 ha0
  · exact card_lt_of_y_no_a0 data hG hKS hK
      (Or.inl rfl) hy0 ha0

/-- Complete `y₂` row, including the possible `a₀`. -/
theorem red_clique_card_lt_of_y2
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy2 : y2 data ∈ K) :
    K.card < k := by
  by_cases ha0 : a0 data ∈ K
  · exact card_lt_of_y_with_a0 data hKS hK
      (Or.inr rfl) hy2 ha0
  · exact card_lt_of_y_no_a0 data hG hKS hK
      (Or.inr rfl) hy2 ha0

/-! ## The `y_*` counting case -/

private theorem core_eq_c0_of_mem_yStar_clique
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K)
    {d : V} (hd : Switching.Vertex.core d ∈ K) :
    d = c0 data := by
  have hyred : redToWA data (yStar data) := hKS hyStar
  have hdred : redToWA data (Switching.Vertex.core d) := hKS hd
  have hfinal :=
    old_adj_implies_final data hyred hdred
      (hK hyStar hd (by simp [yStar]))
  exact (final_adj_yStar_core_iff data d).1 hfinal

private theorem z_not_mem_of_mem_yStar_clique
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K) :
    zVertex ∉ K := by
  intro hz
  have hyred : redToWA data (yStar data) := hKS hyStar
  have hzred : redToWA data zVertex := hKS hz
  have hfinal :=
    old_adj_implies_final data hyred hzred
      (hK hyStar hz (by simp [yStar, zVertex]))
  exact final_not_adj_yStar_z data hfinal

private theorem y_index_eq_none_of_mem_yStar_clique
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K)
    {r : Option (Fin (s - 1))}
    (hr : Switching.Vertex.y data.cert r ∈ K) :
    r = none := by
  have hrred : redToWA data
      (Switching.Vertex.y data.cert r) := hKS hr
  rcases (redToWA_y data r).1 hrred with h | h | h
  · exact h
  · subst r
    have hrem :
        (extraARemovedRedGraph data).Adj
          (y0 data) (yStar data) := by
      rw [extraARemovedRedGraph_adj_iff]
      exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
    exact False.elim
      (extraAOldGraph_not_adj_of_removed data hrem
        (hK hr hyStar (by simp [yStar])))
  · subst r
    have hfinal :=
      old_adj_implies_final data hrred (hKS hyStar)
        (hK hr hyStar (by simp [yStar]))
    exact False.elim (final_not_adj_y2_yStar data hfinal)

private theorem x_index_eq_none_of_mem_red_neighborhood
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    {r : Option (Fin (s - 1))}
    (hr : Switching.Vertex.x data.cert r ∈ K) :
    r = none :=
  (redToWA_x data r).1 (hKS hr)

private theorem a_index_eq_c0_of_core_c0
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hc0 : Switching.Vertex.core (c0 data) ∈ K)
    {p : Fin (k - 1)}
    (hp : Switching.Vertex.a p ∈ K) :
    p = c0Index data := by
  have hfinal :=
    old_adj_implies_final data (hKS hc0) (hKS hp)
      (hK hc0 hp (by simp))
  exact data.cert.c.injective
    ((final_adj_core_a_iff data (c0 data) p).1 hfinal)

private theorem a0_not_mem_of_xStar
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hx : xStar data ∈ K) :
    a0 data ∉ K := by
  intro ha0
  have hfinal :=
    old_adj_implies_final data (hKS hx) (hKS ha0)
      (hK hx ha0 (by simp [xStar, a0]))
  exact final_not_adj_xStar_a0 data hfinal

private theorem not_both_matched
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (p : Fin (k - 1))
    (ha : Switching.Vertex.a p ∈ K)
    (hb : Switching.Vertex.b p ∈ K) :
    False := by
  have hfinal :=
    old_adj_implies_final data (hKS ha) (hKS hb)
      (hK ha hb (by simp))
  exact final_not_adj_a_b_same data p hfinal

private theorem card_aIn_add_card_bIn_le_sub_two
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K) :
    Fintype.card (AIn K) + Fintype.card (BIn K) ≤ k - 2 := by
  classical
  let f :
      (AIn K ⊕ BIn K) ↪
        {p : Fin (k - 1) // p ≠ c2Index data} :=
    { toFun
        | Sum.inl p =>
            ⟨p.1, (redToWA_a data p.1).1 (hKS p.2)⟩
        | Sum.inr p =>
            ⟨p.1, Q_ne_c2 data
              ((redToWA_b data p.1).1 (hKS p.2))⟩
      inj' := by
        intro x y hxy
        rcases x with p | p <;> rcases y with q | q
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inl (Subtype.ext hpq)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqb : Switching.Vertex.b p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 p.2 hqb)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqa : Switching.Vertex.a p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 hqa p.2)
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inr (Subtype.ext hpq) }
  have hcard :=
    Fintype.card_le_of_injective f f.injective
  rw [Fintype.card_sum, card_index_away_from_two data] at hcard
  exact hcard

private theorem card_aIn_add_card_bIn_le_sub_three
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (ha0 : a0 data ∉ K) :
    Fintype.card (AIn K) + Fintype.card (BIn K) ≤ k - 3 := by
  classical
  let f :
      (AIn K ⊕ BIn K) ↪
        {p : Fin (k - 1) //
          ¬(p = c0Index data ∨ p = c2Index data)} :=
    { toFun
        | Sum.inl p =>
            ⟨p.1, by
              rintro (hp0 | hp2)
              · exact ha0 (by simpa [a0, hp0] using p.2)
              · exact (redToWA_a data p.1).1 (hKS p.2) hp2⟩
        | Sum.inr p =>
            ⟨p.1, by
              intro hp
              have hpQ := (redToWA_b data p.1).1 (hKS p.2)
              rcases hp with hp0 | hp2
              · exact Q_ne_c0 data hpQ hp0
              · exact Q_ne_c2 data hpQ hp2⟩
      inj' := by
        intro x y hxy
        rcases x with p | p <;> rcases y with q | q
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inl (Subtype.ext hpq)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqb : Switching.Vertex.b p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 p.2 hqb)
        · have hpq : p.1 = q.1 :=
            congrArg Subtype.val hxy
          have hqa : Switching.Vertex.a p.1 ∈ K := by
            simpa [hpq] using q.2
          exact False.elim
            (not_both_matched data hKS hK p.1 hqa p.2)
        · have hpq : p.1 = q.1 :=
            congrArg (fun z => z.1) hxy
          exact congrArg Sum.inr (Subtype.ext hpq) }
  have hcard :=
    Fintype.card_le_of_injective f f.injective
  rw [Fintype.card_sum,
    card_index_away_from_zero_two data] at hcard
  exact hcard

/-- The `y_*` row, proved by the explicit block-index
count.  No projection into a previously handled `y₀` row is used. -/
theorem red_clique_card_lt_of_yStar
    (data : Certificates.PlusCaseAData G k s)
    (_hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hyStar : yStar data ∈ K) :
    K.card < k := by
  classical
  have hCoreLe : Fintype.card (CoreIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    calc
      p.1 = c0 data :=
        core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar p.2
      _ = q.1 :=
        (core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar q.2).symm
  have hXLe : Fintype.card (XIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    calc
      r.1 = none :=
        x_index_eq_none_of_mem_red_neighborhood data hKS r.2
      _ = t.1 :=
        (x_index_eq_none_of_mem_red_neighborhood
          data hKS t.2).symm
  have hYLe : Fintype.card (YIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    apply Subtype.ext
    calc
      r.1 = none :=
        y_index_eq_none_of_mem_yStar_clique
          data hKS hK hyStar r.2
      _ = t.1 :=
        (y_index_eq_none_of_mem_yStar_clique
          data hKS hK hyStar t.2).symm
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro z
    exact z_not_mem_of_mem_yStar_clique
      data hKS hK hyStar (by simpa using z.2)
  have hBLeQ :
      Fintype.card (BIn K) ≤ (Q data).card := by
    let f : BIn K ↪ {p : Fin (k - 1) // p ∈ Q data} :=
      { toFun := fun p =>
          ⟨p.1, (redToWA_b data p.1).1 (hKS p.2)⟩
        inj' := by
          intro p q hpq
          apply Subtype.ext
          exact congrArg (fun z => z.1) hpq }
    calc
      Fintype.card (BIn K) ≤
          Fintype.card {p : Fin (k - 1) // p ∈ Q data} :=
        Fintype.card_le_of_injective f f.injective
      _ = (Q data).card := Fintype.card_coe _
  have hparts := card_eq_six_blocks data.cert K
  have hQ := card_Q_le data
  have hk := data.cert.five_le_k
  by_cases hc0 : Switching.Vertex.core (c0 data) ∈ K
  · have hALe : Fintype.card (AIn K) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro p q
      apply Subtype.ext
      calc
        p.1 = c0Index data :=
          a_index_eq_c0_of_core_c0 data hKS hK hc0 p.2
        _ = q.1 :=
          (a_index_eq_c0_of_core_c0
            data hKS hK hc0 q.2).symm
    by_cases hx : xStar data ∈ K
    · have hAZero : Fintype.card (AIn K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro p
        have hp0 :=
          a_index_eq_c0_of_core_c0 data hKS hK hc0 p.2
        exact a0_not_mem_of_xStar data hKS hK hx
          (by simpa [a0, hp0] using p.2)
      omega
    · have hXZero :
          Fintype.card (XIn data.cert K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro r
        have hr :=
          x_index_eq_none_of_mem_red_neighborhood data hKS r.2
        exact hx (by simpa [xStar, hr] using r.2)
      omega
  · have hCoreZero : Fintype.card (CoreIn K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro d
      have hd :=
        core_eq_c0_of_mem_yStar_clique
          data hKS hK hyStar d.2
      exact hc0 (by simpa [hd] using d.2)
    by_cases hx : xStar data ∈ K
    · have ha0 := a0_not_mem_of_xStar data hKS hK hx
      have hAB :=
        card_aIn_add_card_bIn_le_sub_three
          data hKS hK ha0
      omega
    · have hXZero :
          Fintype.card (XIn data.cert K) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        intro r
        have hr :=
          x_index_eq_none_of_mem_red_neighborhood data hKS r.2
        exact hx (by simpa [xStar, hr] using r.2)
      have hAB :=
        card_aIn_add_card_bIn_le_sub_two data hKS hK
      omega

/-! ## Red cliques containing no `Y` vertex -/

private theorem member_cases_no_y
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ((∃ p, d = data.cert.c p) ∨ G.Adj (i0 data) d)) ∨
    (∃ p : Fin (k - 1),
      v = Switching.Vertex.a p ∧ p ≠ c2Index data) ∨
    (∃ p : Fin (k - 1),
      p ∈ Q data ∧ v = Switching.Vertex.b p) ∨
    v = xStar data ∨
    v = zVertex := by
  have hvred : redToWA data v := hKS hv
  rcases red_member_cases data hvred with
      hcore | ha | hb | hx | hy0' | hy2' | hys | hz
  · exact Or.inl hcore
  · exact Or.inr (Or.inl ha)
  · obtain ⟨p, hp, hpQ⟩ := hb
    exact Or.inr (Or.inr (Or.inl ⟨p, hpQ, hp⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · subst v
    exact False.elim (hy0 hv)
  · subst v
    exact False.elim (hy2 hv)
  · subst v
    exact False.elim (hyStar hv)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))

private theorem card_yIn_eq_zero_of_no_y
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K) :
    Fintype.card (YIn data.cert K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨r, hr⟩
  have hrred : redToWA data
      (Switching.Vertex.y data.cert r) := hKS hr
  rcases (redToWA_y data r).1 hrred with h | h | h
  · subst r
    exact hyStar hr
  · subst r
    exact hy0 hr
  · subst r
    exact hy2 hr

private theorem card_xIn_eq_zero_of_not_mem
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hx : xStar data ∉ K) :
    Fintype.card (XIn data.cert K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨r, hr⟩
  have hrnone :=
    x_index_eq_none_of_mem_red_neighborhood data hKS hr
  exact hx (by simpa [xStar, hrnone] using hr)

private theorem card_xIn_le_one
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v}) :
    Fintype.card (XIn data.cert K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro r t
  apply Subtype.ext
  calc
    r.1 = none :=
      x_index_eq_none_of_mem_red_neighborhood data hKS r.2
    _ = t.1 :=
      (x_index_eq_none_of_mem_red_neighborhood
        data hKS t.2).symm

private theorem card_zIn_eq_zero_of_not_mem
    {K : Finset (Switching.Vertex V k s)}
    (hz : zVertex ∉ K) :
    Fintype.card (ZIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨u, hu⟩
  cases u
  exact hz hu

private theorem card_bIn_le_card_Q
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v}) :
    Fintype.card (BIn K) ≤ (Q data).card := by
  classical
  let f : BIn K ↪ {p : Fin (k - 1) // p ∈ Q data} :=
    { toFun := fun p =>
        ⟨p.1, (redToWA_b data p.1).1 (hKS p.2)⟩
      inj' := by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun z => z.1) hpq }
  calc
    Fintype.card (BIn K) ≤
        Fintype.card {p : Fin (k - 1) // p ∈ Q data} :=
      Fintype.card_le_of_injective f f.injective
    _ = (Q data).card := Fintype.card_coe _

private theorem card_bIn_eq_zero_of_z
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hz : zVertex ∈ K) :
    Fintype.card (BIn K) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro p
  have hpQ := (redToWA_b data p.1).1 (hKS p.2)
  exact not_old_adj_z_b_of_mem_Q data hpQ
    (hK hz p.2 (by simp [zVertex]))

private theorem card_coreIn_le_one_of_a
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {p : Fin (k - 1)}
    (hp : Switching.Vertex.a p ∈ K) :
    Fintype.card (CoreIn K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro d e
  apply Subtype.ext
  have hpd :=
    old_adj_implies_final data (hKS d.2) (hKS hp)
      (hK d.2 hp (by simp))
  have hpe :=
    old_adj_implies_final data (hKS e.2) (hKS hp)
      (hK e.2 hp (by simp))
  calc
    d.1 = data.cert.c p :=
      ((final_adj_core_a_iff data d.1 p).1 hpd).symm
    _ = e.1 :=
      (final_adj_core_a_iff data e.1 p).1 hpe

private theorem card_aIn_le_one_of_core
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    {d : V}
    (hd : Switching.Vertex.core d ∈ K) :
    Fintype.card (AIn K) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro p q
  apply Subtype.ext
  have hdp :=
    old_adj_implies_final data (hKS hd) (hKS p.2)
      (hK hd p.2 (by simp))
  have hdq :=
    old_adj_implies_final data (hKS hd) (hKS q.2)
      (hK hd q.2 (by simp))
  exact data.cert.c.injective
    (((final_adj_core_a_iff data d p.1).1 hdp).trans
      ((final_adj_core_a_iff data d q.1).1 hdq).symm)

private theorem card_coreIn_eq_zero_of_two_a
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hA : 2 ≤ Fintype.card (AIn K)) :
    Fintype.card (CoreIn K) = 0 := by
  by_cases hempty : IsEmpty (CoreIn K)
  · exact Fintype.card_eq_zero
  · letI : Nonempty (CoreIn K) := not_isEmpty_iff.mp hempty
    let d : CoreIn K := Classical.choice inferInstance
    have hAle := card_aIn_le_one_of_core data hKS hK d.2
    omega

private theorem member_cases_lower
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1), v = Switching.Vertex.a p) ∨
    (∃ p : Fin (k - 1),
      p ∈ Q data ∧ v = Switching.Vertex.b p) := by
  rcases member_cases_no_y data hKS hy0 hy2 hyStar hv with
      hcore | ha | hb | hxs | hzs
  · obtain ⟨d, hd, _⟩ := hcore
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨p, hp, _⟩ := ha
    exact Or.inr (Or.inl ⟨p, hp⟩)
  · exact Or.inr (Or.inr hb)
  · subst v
    exact False.elim (hx hv)
  · subst v
    exact False.elim (hz hv)

private def lowerProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core v)) => .core v
  | .inl (.core (.a p)) => .a p
  | .inl (.core (.b p)) => .b p
  | _ => .a (c0Index data)

@[simp]
private theorem lowerProjection_core
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    lowerProjection data (Switching.Vertex.core v) =
      SpecialLiftVertex.core v :=
  rfl

@[simp]
private theorem lowerProjection_a
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    lowerProjection data (Switching.Vertex.a p) =
      SpecialLiftVertex.a p :=
  rfl

@[simp]
private theorem lowerProjection_b
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    lowerProjection data (Switching.Vertex.b p) =
      SpecialLiftVertex.b p :=
  rfl

private theorem lowerProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (lowerProjection data u) (lowerProjection data v) := by
  have hfinal :=
    old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_lower data hKS hy0 hy2 hyStar hx hz hu with
      ⟨d, rfl⟩ | ⟨p, rfl⟩ | ⟨p, hpQ, rfl⟩ <;>
    rcases member_cases_lower data hKS hy0 hy2 hyStar hx hz hv with
      ⟨e, rfl⟩ | ⟨q, rfl⟩ | ⟨q, hqQ, rfl⟩
  · simpa using (final_adj_core_core_iff data d e).1 hfinal
  · simpa using (final_adj_core_a_iff data d q).1 hfinal
  · simpa using (final_adj_core_b_iff data d q).1 hfinal
  · simpa using (final_adj_core_a_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · simpa using (final_adj_a_a_iff data p q).1 hfinal
  · simpa using (final_adj_a_b_iff data p q).1 hfinal
  · simpa using (final_adj_core_b_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · simpa using (final_adj_a_b_iff data q p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · simpa using
      (final_adj_b_b_iff_of_mem_Q data p q hpQ hqQ).1 hfinal

private theorem card_lt_no_y_no_x_no_z
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∉ K) :
    K.card < k := by
  let f := lowerProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv =>
      lowerProjection_maps_adj data hKS
        hy0 hy2 hyStar hx hz hu hv huv
  have hinj : Set.InjOn f
      (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hFirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ => Set.mem_univ _)
    hadj hFirst.1.cliqueFreeOn hK

private theorem member_cases_z_no_x
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d) ∨
    (∃ p : Fin (k - 1),
      p ≠ c0Index data ∧ v = Switching.Vertex.a p) ∨
    v = zVertex := by
  rcases member_cases_no_y data hKS hy0 hy2 hyStar hv with
      hcore | ha | hb | hxs | hzs
  · obtain ⟨d, hd, _⟩ := hcore
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨p, rfl, _⟩ := ha
    have hp0 : p ≠ c0Index data := by
      intro hp
      subst p
      have hfinal :=
        old_adj_implies_final data (hKS hz) (hKS hv)
          (hK hz hv (by simp [zVertex]))
      exact final_not_adj_z_a0 data hfinal
    exact Or.inr (Or.inl ⟨p, hp0, rfl⟩)
  · obtain ⟨p, hpQ, rfl⟩ := hb
    exact False.elim
      (not_old_adj_z_b_of_mem_Q data hpQ
        (hK hz hv (by simp [zVertex])))
  · subst v
    exact False.elim (hx hv)
  · exact Or.inr (Or.inr hzs)

private def zProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core v)) => .core v
  | .inl (.core (.a p)) => .a p
  | .inr _ => .b (c0Index data)
  | _ => .a (c0Index data)

@[simp]
private theorem zProjection_core
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    zProjection data (Switching.Vertex.core v) =
      SpecialLiftVertex.core v :=
  rfl

@[simp]
private theorem zProjection_a
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    zProjection data (Switching.Vertex.a p) =
      SpecialLiftVertex.a p :=
  rfl

@[simp]
private theorem zProjection_z
    (data : Certificates.PlusCaseAData G k s) :
    zProjection data zVertex =
      SpecialLiftVertex.b (c0Index data) :=
  rfl

private theorem zProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (zProjection data u) (zProjection data v) := by
  have hfinal :=
    old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_z_no_x data hKS hK
      hy0 hy2 hyStar hx hz hu with
      ⟨d, rfl⟩ | ⟨p, hp0, rfl⟩ | rfl <;>
    rcases member_cases_z_no_x data hKS hK
      hy0 hy2 hyStar hx hz hv with
      ⟨e, rfl⟩ | ⟨q, hq0, rfl⟩ | rfl
  · simpa using (final_adj_core_core_iff data d e).1 hfinal
  · simpa using (final_adj_core_a_iff data d q).1 hfinal
  · simpa using
      ((final_adj_z_core_iff data d).1
        ((Switching.finalGraph data.cert).adj_symm hfinal))
  · simpa using (final_adj_core_a_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · simpa using (final_adj_a_a_iff data p q).1 hfinal
  · simpa using
      (specialLift_adj_a_b G data.cert.c p (c0Index data)).2 hp0
  · simpa using (final_adj_z_core_iff data e).1 hfinal
  · simpa using
      (specialLift_adj_b_a G data.cert.c
        (c0Index data) q).2 hq0
  · exact False.elim (huv.ne rfl)

private theorem card_lt_no_y_z_no_x
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∉ K)
    (hz : zVertex ∈ K) :
    K.card < k := by
  let f := zProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv =>
      zProjection_maps_adj data hKS hK
        hy0 hy2 hyStar hx hz hu hv huv
  have hinj : Set.InjOn f
      (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hFirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ => Set.mem_univ _)
    hadj hFirst.1.cliqueFreeOn hK

private theorem c_adj_i0_of_mem_Q
    (data : Certificates.PlusCaseAData G k s)
    {p : Fin (k - 1)} (hpQ : p ∈ Q data) :
    G.Adj (data.cert.c p) (i0 data) := by
  by_contra hred
  exact ((mem_Q data p).1 hpQ).2
    ((mem_P data p).2 hred)

private theorem i0_adj_of_core_with_xStar
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hK : (extraAOldGraph data).IsClique K)
    (hx : xStar data ∈ K)
    {d : V} (hd : Switching.Vertex.core d ∈ K)
    (hdred :
      (∃ p, d = data.cert.c p) ∨ G.Adj (i0 data) d) :
    G.Adj (i0 data) d := by
  rcases hdred with ⟨p, rfl⟩ | hred
  · have hpNot : p ∉ P data := by
      intro hp
      have hrem :
          (extraARemovedRedGraph data).Adj
            (Switching.Vertex.core (data.cert.c p))
            (xStar data) := by
        rw [extraARemovedRedGraph_adj_iff]
        exact Or.inl ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩
      exact extraAOldGraph_not_adj_of_removed data hrem
        (hK hd hx (by simp [xStar]))
    have hcpi : G.Adj (data.cert.c p) (i0 data) := by
      by_contra h
      exact hpNot ((mem_P data p).2 h)
    exact G.adj_symm hcpi
  · exact hred

private theorem member_cases_x_no_a_no_z
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hz : zVertex ∉ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ((∃ p, d = data.cert.c p) ∨ G.Adj (i0 data) d)) ∨
    (∃ p : Fin (k - 1),
      p ∈ Q data ∧ v = Switching.Vertex.b p) ∨
    v = xStar data := by
  rcases member_cases_no_y data hKS hy0 hy2 hyStar hv with
      hcore | hA | hB | hx | hZ
  · exact Or.inl hcore
  · obtain ⟨p, rfl, _⟩ := hA
    exact False.elim (ha p hv)
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr hx)
  · subst v
    exact False.elim (hz hv)

private def xProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → SpecialLiftVertex V k
  | .inl (.core (.core v)) => .core v
  | .inl (.core (.b p)) => .b p
  | .inl (.a _) => .core (i0 data)
  | _ => .core (i0 data)

@[simp]
private theorem xProjection_core
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    xProjection data (Switching.Vertex.core v) =
      SpecialLiftVertex.core v :=
  rfl

@[simp]
private theorem xProjection_b
    (data : Certificates.PlusCaseAData G k s)
    (p : Fin (k - 1)) :
    xProjection data (Switching.Vertex.b p) =
      SpecialLiftVertex.b p :=
  rfl

@[simp]
private theorem xProjection_xStar
    (data : Certificates.PlusCaseAData G k s) :
    xProjection data (xStar data) =
      SpecialLiftVertex.core (i0 data) := by
  simp [xProjection]

private theorem xProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∉ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data).Adj u v) :
    (specialLift G data.cert.c).Adj
      (xProjection data u) (xProjection data v) := by
  have hfinal :=
    old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_x_no_a_no_z data hKS
      hy0 hy2 hyStar ha hz hu with
      ⟨d, rfl, hdred⟩ | ⟨p, hpQ, rfl⟩ | rfl <;>
    rcases member_cases_x_no_a_no_z data hKS
      hy0 hy2 hyStar ha hz hv with
      ⟨e, rfl, hered⟩ | ⟨q, hqQ, rfl⟩ | rfl
  · simpa using (final_adj_core_core_iff data d e).1 hfinal
  · simpa using (final_adj_core_b_iff data d q).1 hfinal
  · simpa using
      (G.adj_symm
        (i0_adj_of_core_with_xStar data hK hx hu hdred))
  · simpa using (final_adj_core_b_iff data e p).1
      ((Switching.finalGraph data.cert).adj_symm hfinal)
  · simpa using
      (final_adj_b_b_iff_of_mem_Q data p q hpQ hqQ).1 hfinal
  · apply (specialLift_adj_b_core G data.cert.c p (i0 data)).2
    exact ⟨(data.cert.c_ne_i p (i0Index data)).symm,
      c_adj_i0_of_mem_Q data hpQ⟩
  · simpa using
      i0_adj_of_core_with_xStar data hK hx hv hered
  · apply (specialLift_adj_core_b G data.cert.c (i0 data) q).2
    exact ⟨(data.cert.c_ne_i q (i0Index data)).symm,
      c_adj_i0_of_mem_Q data hqQ⟩
  · exact False.elim (huv.ne rfl)

private theorem card_lt_no_y_x_no_z_no_a
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∉ K) :
    K.card < k := by
  let f := xProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data).Adj u v →
          (specialLift G data.cert.c).Adj (f u) (f v) :=
    fun {_ _} hu hv huv =>
      xProjection_maps_adj data hKS hK
        hy0 hy2 hyStar ha hx hz hu hv huv
  have hinj : Set.InjOn f
      (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  have hFirst :=
    specialLift_isRamseyFree G data.cert.c
      data.cert.c_isClique data.cert.five_le_k hG
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ => Set.mem_univ _)
    hadj hFirst.1.cliqueFreeOn hK

private theorem card_lt_no_y_x_no_z
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∉ K) :
    K.card < k := by
  classical
  by_cases hAempty : IsEmpty (AIn K)
  · have ha :
        ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K := by
      intro p hp
      exact isEmptyElim (⟨p, hp⟩ : AIn K)
    exact card_lt_no_y_x_no_z_no_a
      data hG hKS hK hy0 hy2 hyStar ha hx hz
  · letI : Nonempty (AIn K) := not_isEmpty_iff.mp hAempty
    let p : AIn K := Classical.choice inferInstance
    have hApos : 0 < Fintype.card (AIn K) :=
      Fintype.card_pos_iff.mpr inferInstance
    have hYZero :=
      card_yIn_eq_zero_of_no_y data hKS hy0 hy2 hyStar
    have hZZero := card_zIn_eq_zero_of_not_mem hz
    have hXLe := card_xIn_le_one data hKS
    have hBLe := card_bIn_le_card_Q data hKS
    have hQ := card_Q_le data
    have hparts := card_eq_six_blocks data.cert K
    have hk := data.cert.five_le_k
    by_cases hAtwo : 2 ≤ Fintype.card (AIn K)
    · have hCoreZero :=
        card_coreIn_eq_zero_of_two_a data hKS hK hAtwo
      have ha0 := a0_not_mem_of_xStar data hKS hK hx
      have hAB :=
        card_aIn_add_card_bIn_le_sub_three
          data hKS hK ha0
      omega
    · have hAOne : Fintype.card (AIn K) = 1 := by
        omega
      have hCoreLe :=
        card_coreIn_le_one_of_a data hKS hK p.2
      omega

private theorem member_cases_x_z_no_a
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hz : zVertex ∈ K)
    {v : Switching.Vertex V k s} (hv : v ∈ K) :
    (∃ d : V, v = Switching.Vertex.core d ∧
      ((∃ p, d = data.cert.c p) ∨ G.Adj (i0 data) d)) ∨
    v = xStar data ∨
    v = zVertex := by
  rcases member_cases_no_y data hKS hy0 hy2 hyStar hv with
      hcore | hA | hB | hx | hZ
  · exact Or.inl hcore
  · obtain ⟨p, rfl, _⟩ := hA
    exact False.elim (ha p hv)
  · obtain ⟨p, hpQ, rfl⟩ := hB
    exact False.elim
      (not_old_adj_z_b_of_mem_Q data hpQ
        (hK hz hv (by simp [zVertex])))
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hZ)

private def xzProjection
    (data : Certificates.PlusCaseAData G k s) :
    Switching.Vertex V k s → V
  | .inl (.core (.core v)) => v
  | .inl (.a _) => i0 data
  | .inr _ => c0 data
  | _ => c0 data

@[simp]
private theorem xzProjection_core
    (data : Certificates.PlusCaseAData G k s) (v : V) :
    xzProjection data (Switching.Vertex.core v) = v :=
  rfl

@[simp]
private theorem xzProjection_xStar
    (data : Certificates.PlusCaseAData G k s) :
    xzProjection data (xStar data) = i0 data := by
  simp [xzProjection]

@[simp]
private theorem xzProjection_z
    (data : Certificates.PlusCaseAData G k s) :
    xzProjection data zVertex = c0 data :=
  rfl

private theorem xzProjection_maps_adj
    (data : Certificates.PlusCaseAData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∈ K)
    {u v : Switching.Vertex V k s}
    (hu : u ∈ K) (hv : v ∈ K)
    (huv : (extraAOldGraph data).Adj u v) :
    G.Adj (xzProjection data u) (xzProjection data v) := by
  have hfinal :=
    old_adj_implies_final data (hKS hu) (hKS hv) huv
  rcases member_cases_x_z_no_a data hKS hK
      hy0 hy2 hyStar ha hz hu with
      ⟨d, rfl, hdred⟩ | rfl | rfl <;>
    rcases member_cases_x_z_no_a data hKS hK
      hy0 hy2 hyStar ha hz hv with
      ⟨e, rfl, hered⟩ | rfl | rfl
  · simpa using (final_adj_core_core_iff data d e).1 hfinal
  · simpa using
      (G.adj_symm
        (i0_adj_of_core_with_xStar data hK hx hu hdred))
  · simpa using
      (((final_adj_z_core_iff data d).1
        ((Switching.finalGraph data.cert).adj_symm hfinal)).2.symm)
  · simpa using
      i0_adj_of_core_with_xStar data hK hx hv hered
  · exact False.elim (huv.ne rfl)
  · simpa using G.adj_symm data.c0_i0_red
  · simpa using ((final_adj_z_core_iff data e).1 hfinal).2
  · simpa using data.c0_i0_red
  · exact False.elim (huv.ne rfl)

private theorem card_lt_no_y_x_z_no_a
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (ha : ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∈ K) :
    K.card < k := by
  let f := xzProjection data
  have hadj :
      ∀ ⦃u v⦄, u ∈ K → v ∈ K →
        (extraAOldGraph data).Adj u v →
          G.Adj (f u) (f v) :=
    fun {_ _} hu hv huv =>
      xzProjection_maps_adj data hKS hK
        hy0 hy2 hyStar ha hx hz hu hv huv
  have hinj : Set.InjOn f
      (K : Set (Switching.Vertex V k s)) := by
    intro u hu v hv huv
    by_contra hne
    exact (hadj hu hv (hK hu hv hne)).ne huv
  exact card_lt_of_cliqueFreeOn_of_injOn
    f hinj (fun {_} _ => Set.mem_univ _)
    hadj hG.1.cliqueFreeOn hK

private theorem card_lt_no_y_x_z
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K)
    (hx : xStar data ∈ K)
    (hz : zVertex ∈ K) :
    K.card < k := by
  classical
  by_cases hAempty : IsEmpty (AIn K)
  · have ha :
        ∀ p : Fin (k - 1), Switching.Vertex.a p ∉ K := by
      intro p hp
      exact isEmptyElim (⟨p, hp⟩ : AIn K)
    exact card_lt_no_y_x_z_no_a
      data hG hKS hK hy0 hy2 hyStar ha hx hz
  · letI : Nonempty (AIn K) := not_isEmpty_iff.mp hAempty
    let p : AIn K := Classical.choice inferInstance
    have hApos : 0 < Fintype.card (AIn K) :=
      Fintype.card_pos_iff.mpr inferInstance
    have hYZero :=
      card_yIn_eq_zero_of_no_y data hKS hy0 hy2 hyStar
    have hBZero := card_bIn_eq_zero_of_z data hKS hK hz
    have hXLe := card_xIn_le_one data hKS
    have hZLe := card_zIn_le_one K
    have hparts := card_eq_six_blocks data.cert K
    have hk := data.cert.five_le_k
    by_cases hAtwo : 2 ≤ Fintype.card (AIn K)
    · have hCoreZero :=
        card_coreIn_eq_zero_of_two_a data hKS hK hAtwo
      have ha0 := a0_not_mem_of_xStar data hKS hK hx
      have hAB :=
        card_aIn_add_card_bIn_le_sub_three
          data hKS hK ha0
      omega
    · have hAOne : Fintype.card (AIn K) = 1 := by
        omega
      have hCoreLe :=
        card_coreIn_le_one_of_a data hKS hK p.2
      omega

private theorem red_clique_card_lt_of_no_y
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hKS : (K : Set (Switching.Vertex V k s)) ⊆
      {v | redToWA data v})
    (hK : (extraAOldGraph data).IsClique K)
    (hy0 : y0 data ∉ K)
    (hy2 : y2 data ∉ K)
    (hyStar : yStar data ∉ K) :
    K.card < k := by
  by_cases hx : xStar data ∈ K
  · by_cases hz : zVertex ∈ K
    · exact card_lt_no_y_x_z
        data hG hKS hK hy0 hy2 hyStar hx hz
    · exact card_lt_no_y_x_no_z
        data hG hKS hK hy0 hy2 hyStar hx hz
  · by_cases hz : zVertex ∈ K
    · exact card_lt_no_y_z_no_x
        data hG hKS hK hy0 hy2 hyStar hx hz
    · exact card_lt_no_y_no_x_no_z
        data hG hKS hK hy0 hy2 hyStar hx hz

/-- The red neighborhood of the second Type A connector
contains no red `K_k`. -/
theorem redNeighborhoodA_cliqueFree
    (data : Certificates.PlusCaseAData G k s)
    (hG : IsRamseyFree G k s) :
    (extraAOldGraph data).CliqueFreeOn
      {v | redToWA data v} k := by
  intro K hKS hK
  have hlt : K.card < k := by
    by_cases hy0 : y0 data ∈ K
    · exact red_clique_card_lt_of_y0
        data hG hKS hK.isClique hy0
    · by_cases hy2 : y2 data ∈ K
      · exact red_clique_card_lt_of_y2
          data hG hKS hK.isClique hy2
      · by_cases hyStar : yStar data ∈ K
        · exact red_clique_card_lt_of_yStar
            data hG hKS hK.isClique hyStar
        · exact red_clique_card_lt_of_no_y
            data hG hKS hK.isClique hy0 hy2 hyStar
  have hcard := hK.card_eq
  omega

end TypeA
end SecondConnector
end RamseyIncrement
