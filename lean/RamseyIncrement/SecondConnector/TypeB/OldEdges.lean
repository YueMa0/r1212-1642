/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SecondConnector.TypeB.ChangedEdges
import RamseyIncrement.SecondConnector.Projection
import RamseyIncrement.Switching.Theorem

/-!
# Safety of the edited Type B old graph

This file proves the two common-neighborhood rows of the strengthened
Type B second-connector argument:

* B-R: the newly red edge `i₂a₂`;
* B-B: the newly blue edge `c₂x_*`.

The generic dangerous-edge reduction then shows that the two declarative
edits preserve `(k+1,s+1)`-freeness.
-/

namespace RamseyIncrement
namespace SecondConnector
namespace TypeB

open Finset
open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

private abbrev c2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.c (c2Index data)

private abbrev i2
    (data : Certificates.PlusCaseBData G k s) : V :=
  data.cert.i (i2Index data)

private abbrev a2
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.a (c2Index data)

private abbrev xStar
    (data : Certificates.PlusCaseBData G k s) :
    Switching.Vertex V k s :=
  Switching.Vertex.x data.cert none

private noncomputable abbrev RedGraph
    (data : Certificates.PlusCaseBData G k s) :=
  extraBOldGraph data

private noncomputable abbrev BlueGraph
    (data : Certificates.PlusCaseBData G k s) :=
  (extraBOldGraph data)ᶜ

private theorem c_adj_i2_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    G.Adj (data.cert.c p) (i2 data) ↔ p ≠ c2Index data := by
  constructor
  · intro h hp
    subst p
    have hblue :=
      data.cert.caseB_not_adj_matched data.baseB (c2Index data)
    rw [Certificates.castIndex_c2'
      data.cert.five_le_k data.cert.five_le_s
      data.baseB.k_le_s] at hblue
    exact hblue h
  · intro hp
    have hred :=
      data.cert.caseB_adj_of_ne data.baseB hp
    rw [Certificates.castIndex_c2'
      data.cert.five_le_k data.cert.five_le_s
      data.baseB.k_le_s] at hred
    exact hred

private theorem i_ne_c
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) (p : Fin (k - 1)) :
    data.cert.i q ≠ data.cert.c p :=
  (data.cert.c_ne_i p q).symm

private theorem c0_ne_c2
    (data : Certificates.PlusCaseBData G k s) :
    Certificates.c0Index data.cert.five_le_k ≠ c2Index data := by
  intro h
  have hval := congrArg Fin.val h
  simp [c2Index, Certificates.c0Index] at hval

private theorem final_adj_core_core_iff
    (data : Certificates.PlusCaseBData G k s)
    (v w : V) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.core w) ↔
        G.Adj v w := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_core]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_core_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.a p) ↔
        data.cert.c p = v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_core_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.b p) ↔
        data.cert.c p ≠ v ∧ G.Adj (data.cert.c p) v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_core_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair, ne_comm]

private theorem final_adj_core_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (r : Option (Fin (s - 1))) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.x data.cert r) ↔
        Canonical.secondCertificateAt data.cert.toCertificates
          data.cert.five_le_k r ≠ SpecialLiftVertex.core v := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_x_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem final_adj_core_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) (r : Option (Fin (s - 1))) :
    (Switching.finalGraph data.cert).Adj
      (Switching.Vertex.core v) (Switching.Vertex.y data.cert r) ↔
        SpecialLiftVertex.core v =
            Canonical.secondCertificateAt data.cert.toCertificates
              data.cert.five_le_k r ∨
          (specialLift G data.cert.c).Adj
            (Canonical.secondCertificateAt data.cert.toCertificates
              data.cert.five_le_k r)
            (SpecialLiftVertex.core v) := by
  rw [Switching.final_adj_iff,
    Switching.preGraph_adj_lower_y_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff, Switching.SymmPair]

private theorem red_adj_i2_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data))
      (Switching.Vertex.b p) ↔ p ≠ c2Index data := by
  rw [extraBOldGraph_adj_iff, final_adj_core_b_iff]
  have hne : data.cert.c p ≠ i2 data :=
    (i_ne_c data (i2Index data) p).symm
  simp [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hne, c_adj_i2_iff]

private theorem red_adj_i2_core_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data))
      (Switching.Vertex.core v) ↔ G.Adj (i2 data) v := by
  rw [extraBOldGraph_adj_iff, final_adj_core_core_iff]
  simp [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]

private theorem red_adj_a2_core_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) :
    (RedGraph data).Adj (a2 data) (Switching.Vertex.core v) ↔
      v = c2 data ∨ v = i2 data := by
  rw [(RedGraph data).adj_comm, extraBOldGraph_adj_iff,
    final_adj_core_a_iff]
  simp [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, eq_comm]

private theorem red_adj_i2_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data))
      (Switching.Vertex.a p) ↔ p = c2Index data := by
  rw [extraBOldGraph_adj_iff, final_adj_core_a_iff]
  have hne : data.cert.c p ≠ i2 data :=
    (i_ne_c data (i2Index data) p).symm
  simp [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hne, eq_comm]

private theorem red_adj_a2_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj (a2 data) (Switching.Vertex.a p) ↔
      p ≠ c2Index data := by
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_a]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, ne_comm]

private theorem red_adj_a2_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj (a2 data) (Switching.Vertex.b p) ↔
      p ≠ c2Index data := by
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_a_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, ne_comm]

private theorem red_adj_i2_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data))
      (Switching.Vertex.x data.cert r) ↔
        r ≠ some (i2Index data) := by
  rw [extraBOldGraph_adj_iff, final_adj_core_x_iff]
  simp only [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]
  cases r with
  | none =>
      have hne := i_ne_c data (i2Index data) (c2Index data)
      simp [Canonical.secondCertificateAt, hne]
  | some q =>
      simp [Canonical.secondCertificateAt,
        data.cert.i.injective.eq_iff]

private theorem red_adj_a2_x
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj (a2 data)
      (Switching.Vertex.x data.cert r) := by
  have h02raw :
      Certificates.c0Index data.cert.five_le_k ≠
        Certificates.c2Index data.cert.five_le_k :=
    c0_ne_c2 data
  have h20raw :
      Certificates.c2Index data.cert.five_le_k ≠
        Certificates.c0Index data.cert.five_le_k :=
    h02raw.symm
  rw [extraBOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · rw [Switching.preGraph_adj_lower_x_iff]
      cases r <;>
        simp [Canonical.secondCertificateAt, h02raw]
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair, h20raw]
  · simp [extraBRemovedRedRel, Switching.SymmPair]

private theorem red_adj_i2_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data))
      (Switching.Vertex.y data.cert r) ↔
        r = some (i2Index data) := by
  rw [extraBOldGraph_adj_iff, final_adj_core_y_iff]
  simp only [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]
  cases r with
  | none =>
      have hne := (i_ne_c data (i2Index data)
        (Certificates.c0Index data.cert.five_le_k)).symm
      simp [Canonical.secondCertificateAt, hne]
  | some q =>
      by_cases hq : q = i2Index data
      · subst q
        simp [Canonical.secondCertificateAt]
      · have hblue : Gᶜ.Adj (data.cert.i q) (i2 data) :=
          data.cert.i_compl_adj hq
        have hnred : ¬G.Adj (data.cert.i q) (i2 data) :=
          (SimpleGraph.compl_adj _ _ _).1 hblue |>.2
        simp [Canonical.secondCertificateAt, hq, hnred,
          data.cert.i.injective.eq_iff, Ne.symm hq]

private theorem red_adj_a2_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj (a2 data)
      (Switching.Vertex.y data.cert r) ↔ r = none := by
  have h02raw :
      Certificates.c0Index data.cert.five_le_k ≠
        Certificates.c2Index data.cert.five_le_k :=
    c0_ne_c2 data
  have h20raw :
      Certificates.c2Index data.cert.five_le_k ≠
        Certificates.c0Index data.cert.five_le_k :=
    h02raw.symm
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff,
    Switching.preGraph_adj_lower_y_iff]
  simp only [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    Switching.SymmPair]
  cases r with
  | none =>
      simp [Canonical.secondCertificateAt, h02raw, h20raw]
  | some q =>
      have hne : data.cert.c (c2Index data) ≠ data.cert.i q :=
        data.cert.c_ne_i (c2Index data) q
      simp [Canonical.secondCertificateAt, hne, h20raw]

private theorem red_adj_i2_z
    (data : Certificates.PlusCaseBData G k s) :
    (RedGraph data).Adj
      (Switching.Vertex.core (i2 data)) Switching.Vertex.z := by
  rw [extraBOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · rw [(Switching.preGraph data.cert).adj_comm]
      have hb :
          (Switching.preGraph data.cert).Adj
            (Switching.Vertex.b
              (Certificates.c0Index data.cert.five_le_k))
            (Switching.Vertex.core (i2 data)) := by
        rw [Switching.preGraph_adj_lower_lower_iff,
          specialLift_adj_b_core]
        constructor
        · exact i_ne_c data (i2Index data)
            (Certificates.c0Index data.cert.five_le_k)
        · rw [c_adj_i2_iff]
          exact c0_ne_c2 data
      change (Switching.redJoinedClone
        (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.core (.core (i2 data))))
      rw [Switching.redJoinedClone.adj_z_old]
      right
      simpa [Switching.preGraph] using hb
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair]
  · simp [extraBRemovedRedRel, Switching.SymmPair]

private theorem red_adj_a2_z
    (data : Certificates.PlusCaseBData G k s) :
    (RedGraph data).Adj (a2 data) Switching.Vertex.z := by
  rw [extraBOldGraph_adj_iff]
  left
  constructor
  · rw [Switching.final_adj_iff]
    left
    constructor
    · rw [(Switching.preGraph data.cert).adj_comm]
      have hb :
          (Switching.preGraph data.cert).Adj
            (Switching.Vertex.b
              (Certificates.c0Index data.cert.five_le_k))
            (a2 data) := by
        rw [Switching.preGraph_adj_lower_lower_iff,
          specialLift_adj_b_a]
        exact (c0_ne_c2 data).symm
      change (Switching.redJoinedClone
        (Switching.canonicalGraph data.cert)
        (.core (.b (Switching.Vertex.c0 data.cert)))).Adj
          Switching.CloneVertex.z
          (.inl (.core (.a (c2Index data))))
      rw [Switching.redJoinedClone.adj_z_old]
      right
      simpa [Switching.preGraph] using hb
    · rw [Switching.removedRedGraph_adj_iff]
      simp [Switching.SymmPair]
  · simp [extraBRemovedRedRel, Switching.SymmPair]

/-- Structural form of the common red neighborhood in row B-R. -/
private theorem common_red_i2_a2_cases
    (data : Certificates.PlusCaseBData G k s)
    {w : Switching.Vertex V k s}
    (hw : w ∈ (RedGraph data).commonNeighbors
      (Switching.Vertex.core (i2 data)) (a2 data)) :
    (∃ p, p ≠ c2Index data ∧ w = Switching.Vertex.b p) ∨
    (∃ r, r ≠ some (i2Index data) ∧
      w = Switching.Vertex.x data.cert r) ∨
      w = Switching.Vertex.z := by
  obtain ⟨hi, ha⟩ :=
    (RedGraph data).mem_commonNeighbors.1 hw
  rcases vertex_six_block_cases data.cert w with
    h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    rcases (red_adj_a2_core_iff data v).1 ha with hv | hv
    · subst v
      exact False.elim
        ((c_adj_i2_iff data (c2Index data)).1
          (G.adj_symm
            ((red_adj_i2_core_iff data (c2 data)).1 hi)) rfl)
    · subst v
      exact False.elim ((RedGraph data).loopless.irrefl _ hi)
  · obtain ⟨p, rfl⟩ := h
    have hp2 := (red_adj_i2_a_iff data p).1 hi
    exact False.elim ((red_adj_a2_a_iff data p).1 ha hp2)
  · obtain ⟨p, rfl⟩ := h
    exact Or.inl ⟨p, (red_adj_i2_b_iff data p).1 hi, rfl⟩
  · obtain ⟨r, rfl⟩ := h
    exact Or.inr (Or.inl
      ⟨r, (red_adj_i2_x_iff data r).1 hi, rfl⟩)
  · obtain ⟨r, rfl⟩ := h
    have hi' := (red_adj_i2_y_iff data r).1 hi
    have ha' := (red_adj_a2_y_iff data r).1 ha
    subst r
    simp at ha'
  · subst w
    exact Or.inr (Or.inr rfl)

private theorem red_adj_b_b_iff_of_ne_c2
    (data : Certificates.PlusCaseBData G k s)
    {p q : Fin (k - 1)}
    (hp2 : p ≠ c2Index data) (hq2 : q ≠ c2Index data) :
    (RedGraph data).Adj
        (Switching.Vertex.b p) (Switching.Vertex.b q) ↔
      p ≠ q ∧ SameBPart p q := by
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff,
    Switching.preGraph_adj_lower_lower_iff,
    specialLift_adj_b_b]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hp2, hq2]

private theorem not_red_adj_x_x
    (data : Certificates.PlusCaseBData G k s)
    (r t : Option (Fin (s - 1))) :
    ¬(RedGraph data).Adj
      (Switching.Vertex.x data.cert r)
      (Switching.Vertex.x data.cert t) := by
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.preGraph_not_adj_x_x,
    Switching.addedRedGraph_adj_iff,
    extraBAddedRedRel, Switching.SymmPair]

private theorem final_adj_z_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (Switching.finalGraph data.cert).Adj
        Switching.Vertex.z (Switching.Vertex.b p) ↔
      p = Certificates.c0Index data.cert.five_le_k ∨
        (Certificates.c0Index data.cert.five_le_k ≠ p ∧
          SameBPart
            (Certificates.c0Index data.cert.five_le_k) p) := by
  simp [Switching.finalGraph, Switching.preGraph,
    Switching.removedRedGraph, Switching.removedRedRel,
    Switching.addedRedGraph, Switching.addedRedRel,
    Switching.canonicalGraph, Canonical.graph,
    Switching.Vertex.b]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, (h.2 h.1).2⟩
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, fun hn ↦ ⟨hn, h.2⟩⟩

private theorem red_adj_z_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj
        Switching.Vertex.z (Switching.Vertex.b p) ↔
      p = Certificates.c0Index data.cert.five_le_k ∨
        (Certificates.c0Index data.cert.five_le_k ≠ p ∧
          SameBPart
            (Certificates.c0Index data.cert.five_le_k) p) := by
  rw [extraBOldGraph_adj_iff, final_adj_z_b_iff]
  simp [extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]

private theorem red_adj_z_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj Switching.Vertex.z
        (Switching.Vertex.x data.cert r) ↔
      r = some (Switching.Vertex.i1 data.cert) ∨ r = none := by
  have hpre :
      (Switching.preGraph data.cert).Adj Switching.Vertex.z
        (Switching.Vertex.x data.cert r) :=
    Switching.preGraph_adj_z_x data.cert r
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hpre]
  cases r with
  | none => simp
  | some q =>
      by_cases hq : q = Switching.Vertex.i1 data.cert <;>
        simp [hq, ne_comm]

private theorem red_adj_b0_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj
        (Switching.Vertex.b
          (Certificates.c0Index data.cert.five_le_k))
        (Switching.Vertex.x data.cert r) ↔
      r ≠ some (Switching.Vertex.i1 data.cert) ∧ r ≠ none := by
  have hpre :
      (Switching.preGraph data.cert).Adj
        (Switching.Vertex.b
          (Certificates.c0Index data.cert.five_le_k))
        (Switching.Vertex.x data.cert r) := by
    rw [Switching.preGraph_adj_lower_x_iff]
    cases r <;> simp [Canonical.secondCertificateAt]
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hpre,
    c0_ne_c2 data]

private theorem b_ne_c2_of_mem_red_common
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1))
    (hp : Switching.Vertex.b p ∈
      (RedGraph data).commonNeighbors
        (Switching.Vertex.core (i2 data)) (a2 data)) :
    p ≠ c2Index data := by
  rcases common_red_i2_a2_cases data hp with h | h | h
  · obtain ⟨q, hq, heq⟩ := h
    have hpq : p = q :=
      vertex_b_injective heq
    simpa [hpq] using hq
  · obtain ⟨r, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · have := congrArg blockTag h
    simp at this

private theorem x_ne_i2_of_mem_red_common
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1)))
    (hr : Switching.Vertex.x data.cert r ∈
      (RedGraph data).commonNeighbors
        (Switching.Vertex.core (i2 data)) (a2 data)) :
    r ≠ some (i2Index data) := by
  rcases common_red_i2_a2_cases data hr with h | h | h
  · obtain ⟨p, _, heq⟩ := h
    have := congrArg blockTag heq
    simp at this
  · obtain ⟨t, ht, heq⟩ := h
    have hrt : r = t :=
      (vertex_x_injective data.cert) heq
    simpa [hrt] using ht
  · have := congrArg blockTag h
    simp at this

private theorem card_bIn_le_sub_three
    (data : Certificates.PlusCaseBData G k s)
    {K : Finset (Switching.Vertex V k s)}
    (hpair : ∀ p q : BIn K, p ≠ q →
      SameBPart p.1 q.1) :
    Fintype.card (BIn K) ≤ k - 3 := by
  classical
  by_cases hempty : IsEmpty (BIn K)
  · have : Fintype.card (BIn K) = 0 := Fintype.card_eq_zero
    omega
  · letI : Nonempty (BIn K) := not_isEmpty_iff.mp hempty
    let q₀ : BIn K := Classical.choice inferInstance
    by_cases hsmall : q₀.1.1 < 2
    · have hall : ∀ q : BIn K, q.1.1 < 2 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using hsmall
        · rcases hpair q q₀ hq with h | h
          · exact h.1
          · omega
      let f : BIn K ↪ Fin 2 :=
        { toFun := fun q ↦ ⟨q.1.1, hall q⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin 2 ↦ x.val) hpq }
      have hcard : Fintype.card (BIn K) ≤ 2 := by
        simpa using Fintype.card_le_of_injective f f.injective
      have hk := data.cert.five_le_k
      omega
    · have hall : ∀ q : BIn K, 2 ≤ q.1.1 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using Nat.le_of_not_gt hsmall
        · rcases hpair q q₀ hq with h | h
          · omega
          · exact h.1
      let f : BIn K ↪ Fin (k - 3) :=
        { toFun := fun q ↦
            ⟨q.1.1 - 2, by
              have hlt := q.1.2
              omega⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            have hv := congrArg Fin.val hpq
            dsimp at hv
            have hp := hall p
            have hq := hall q
            omega }
      simpa using Fintype.card_le_of_injective f f.injective

/-- Row B-R: deleting the endpoints `i₂,a₂` leaves no red
`K_(k-1)` in their common neighborhood. -/
theorem red_common_i2_a2_cliqueFree
    (data : Certificates.PlusCaseBData G k s) :
    (RedGraph data).CliqueFreeOn
      ((RedGraph data).commonNeighbors
        (Switching.Vertex.core (i2 data)) (a2 data))
      (k - 1) := by
  classical
  intro K hKsub hK
  have hCoreZero : Fintype.card (CoreIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_red_i2_a2_cases data (hKsub d.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hAZero : Fintype.card (AIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro a
    rcases common_red_i2_a2_cases data (hKsub a.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hYZero : Fintype.card (YIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro y
    rcases common_red_i2_a2_cases data (hKsub y.2) with h | h | h
    · obtain ⟨p, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · obtain ⟨r, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
    · have := congrArg blockTag h
      simp at this
  have hBpair :
      ∀ p q : BIn K, p ≠ q → SameBPart p.1 q.1 := by
    intro p q hpq
    have hp2 := b_ne_c2_of_mem_red_common data p.1 (hKsub p.2)
    have hq2 := b_ne_c2_of_mem_red_common data q.1 (hKsub q.2)
    have hpqv :
        (Switching.Vertex.b p.1 : Switching.Vertex V k s) ≠
          Switching.Vertex.b q.1 := by
      intro h
      apply hpq
      apply Subtype.ext
      exact vertex_b_injective h
    exact (red_adj_b_b_iff_of_ne_c2 data hp2 hq2).1
      (hK.isClique p.2 q.2 hpqv) |>.2
  have hBle : Fintype.card (BIn K) ≤ k - 3 :=
    card_bIn_le_sub_three data hBpair
  have hXle : Fintype.card (XIn data.cert K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro r t
    by_contra hrt
    have hrtv :
        Switching.Vertex.x data.cert r.1 ≠
          Switching.Vertex.x data.cert t.1 := by
      intro h
      apply hrt
      apply Subtype.ext
      exact (vertex_x_injective data.cert) h
    exact not_red_adj_x_x data r.1 t.1
      (hK.isClique r.2 t.2 hrtv)
  have hZle : Fintype.card (ZIn K) ≤ 1 :=
    card_zIn_le_one K
  have hparts := card_eq_six_blocks data.cert K
  have hcard := hK.card_eq
  by_cases hz : (Switching.Vertex.z : Switching.Vertex V k s) ∈ K
  · have hBsmall : ∀ p : BIn K, p.1.val < 2 := by
      intro p
      have hzp :
          (RedGraph data).Adj Switching.Vertex.z
            (Switching.Vertex.b p.1) :=
        hK.isClique hz p.2 (by simp)
      rcases (red_adj_z_b_iff data p.1).1 hzp with hp0 | hp
      · have hpval := congrArg Fin.val hp0
        simp [Certificates.c0Index] at hpval
        omega
      · rcases hp.2 with hpSmall | hpLarge
        · exact hpSmall.2
        · have h0 : ¬2 ≤
              (Certificates.c0Index data.cert.five_le_k).val := by
            simp [Certificates.c0Index]
          exact False.elim (h0 hpLarge.1)
    have hBtwo : Fintype.card (BIn K) ≤ 2 := by
      let f : BIn K ↪ Fin 2 :=
        { toFun := fun p ↦ ⟨p.1.val, hBsmall p⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin 2 ↦ x.val) hpq }
      simpa using Fintype.card_le_of_injective f f.injective
    by_cases hXempty : IsEmpty (XIn data.cert K)
    · have hXzero : Fintype.card (XIn data.cert K) = 0 :=
        Fintype.card_eq_zero
      have hk := data.cert.five_le_k
      omega
    · letI : Nonempty (XIn data.cert K) :=
        not_isEmpty_iff.mp hXempty
      let r₀ : XIn data.cert K := Classical.choice inferInstance
      have hrCases :
          r₀.1 = some (Switching.Vertex.i1 data.cert) ∨
            r₀.1 = none := by
        have hzr :
            (RedGraph data).Adj Switching.Vertex.z
              (Switching.Vertex.x data.cert r₀.1) :=
          hK.isClique hz r₀.2 (by simp)
        exact (red_adj_z_x_iff data r₀.1).1 hzr
      have hBnot0 :
          ∀ p : BIn K,
            p.1 ≠ Certificates.c0Index data.cert.five_le_k := by
        intro p hp0
        have hpr :
            (RedGraph data).Adj
              (Switching.Vertex.b
                (Certificates.c0Index data.cert.five_le_k))
              (Switching.Vertex.x data.cert r₀.1) := by
          rw [← hp0]
          exact hK.isClique p.2 r₀.2 (by simp)
        have hboth := (red_adj_b0_x_iff data r₀.1).1 hpr
        rcases hrCases with hr | hr
        · exact hboth.1 hr
        · exact hboth.2 hr
      have hBone : Fintype.card (BIn K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro p q
        apply Subtype.ext
        apply Fin.ext
        have hpSmall := hBsmall p
        have hqSmall := hBsmall q
        have hp0 := hBnot0 p
        have hq0 := hBnot0 q
        have hpval : p.1.val = 1 := by
          have : p.1.val ≠ 0 := by
            intro hp
            apply hp0
            apply Fin.ext
            simpa [Certificates.c0Index] using hp
          omega
        have hqval : q.1.val = 1 := by
          have : q.1.val ≠ 0 := by
            intro hq
            apply hq0
            apply Fin.ext
            simpa [Certificates.c0Index] using hq
          omega
        omega
      have hk := data.cert.five_le_k
      omega
  · have hZzero : Fintype.card (ZIn K) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro z
      exact hz (by simpa using z.2)
    have hk := data.cert.five_le_k
    omega

private theorem red_adj_core_xStar_iff
    (data : Certificates.PlusCaseBData G k s)
    (v : V) :
    (RedGraph data).Adj
        (Switching.Vertex.core v) (xStar data) ↔
      v ≠ c2 data := by
  rw [extraBOldGraph_adj_iff, final_adj_core_x_iff]
  simp [Canonical.secondCertificateAt,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]

private theorem red_adj_xStar_a_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj (xStar data) (Switching.Vertex.a p) ↔
      p ≠ Certificates.c0Index data.cert.five_le_k := by
  rw [(RedGraph data).adj_comm, extraBOldGraph_adj_iff,
    Switching.final_adj_iff,
    Switching.preGraph_adj_lower_x_iff]
  simp [Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, ne_comm]

private theorem red_adj_xStar_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj (xStar data) (Switching.Vertex.b p) ↔
      p ≠ Certificates.c0Index data.cert.five_le_k := by
  rw [(RedGraph data).adj_comm, extraBOldGraph_adj_iff,
    Switching.final_adj_iff,
    Switching.preGraph_adj_lower_x_iff]
  simp [Canonical.secondCertificateAt,
    Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair]

private theorem red_adj_c2_b_iff
    (data : Certificates.PlusCaseBData G k s)
    (p : Fin (k - 1)) :
    (RedGraph data).Adj
        (Switching.Vertex.core (c2 data))
        (Switching.Vertex.b p) ↔
      p ≠ c2Index data := by
  have hrem : ¬extraBRemovedRedRel data
      (Switching.Vertex.core (c2 data))
      (Switching.Vertex.b p) := by
    simp [extraBRemovedRedRel, Switching.SymmPair]
  have hadd : ¬extraBAddedRedRel data
      (Switching.Vertex.core (c2 data))
      (Switching.Vertex.b p) := by
    simp [extraBAddedRedRel, Switching.SymmPair]
  rw [extraBOldGraph_adj_iff, final_adj_core_b_iff]
  simp only [hrem, hadd, not_false_eq_true, and_true, or_false]
  constructor
  · intro h hp
    subst p
    exact h.1 rfl
  · intro hp
    refine ⟨?_, ?_⟩
    · intro h
      exact hp (data.cert.c.injective h)
    · exact data.cert.c_adj hp

private theorem red_adj_c2_x_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj
        (Switching.Vertex.core (c2 data))
        (Switching.Vertex.x data.cert r) ↔
      r ≠ none := by
  rw [extraBOldGraph_adj_iff, final_adj_core_x_iff]
  cases r with
  | none =>
      simp [Canonical.secondCertificateAt,
        extraBRemovedRedRel, extraBAddedRedRel,
        Switching.SymmPair]
  | some q =>
      have hne :
          data.cert.i q ≠ c2 data :=
        i_ne_c data q (c2Index data)
      simp [Canonical.secondCertificateAt,
        extraBRemovedRedRel, extraBAddedRedRel,
        Switching.SymmPair, hne]

private theorem red_adj_xStar_y_iff
    (data : Certificates.PlusCaseBData G k s)
    (r : Option (Fin (s - 1))) :
    (RedGraph data).Adj (xStar data)
        (Switching.Vertex.y data.cert r) ↔ r = none := by
  rw [extraBOldGraph_adj_iff, Switching.final_adj_iff,
    Switching.preGraph_adj_x_y_iff]
  simp [Switching.removedRedGraph_adj_iff,
    Switching.addedRedGraph_adj_iff,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, eq_comm]

private theorem red_adj_c2_ySome_iff
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1)) :
    (RedGraph data).Adj
        (Switching.Vertex.core (c2 data))
        (Switching.Vertex.y data.cert (some q)) ↔
      G.Adj (c2 data) (data.cert.i q) := by
  rw [extraBOldGraph_adj_iff, final_adj_core_y_iff]
  have hne : c2 data ≠ data.cert.i q :=
    data.cert.c_ne_i (c2Index data) q
  simp [Canonical.secondCertificateAt,
    extraBRemovedRedRel, extraBAddedRedRel,
    Switching.SymmPair, hne, G.adj_comm]

private theorem red_adj_xStar_z
    (data : Certificates.PlusCaseBData G k s) :
    (RedGraph data).Adj (xStar data) Switching.Vertex.z := by
  rw [(RedGraph data).adj_comm, red_adj_z_x_iff]
  exact Or.inr rfl

private theorem c2_adj_i0
    (data : Certificates.PlusCaseBData G k s) :
    G.Adj (c2 data)
      (data.cert.i
        (Certificates.i0Index' data.cert.five_le_s)) := by
  have h :=
    data.cert.caseB_adj_of_ne data.baseB
      (p := Certificates.c0Index data.cert.five_le_k)
      (r := c2Index data)
      (by
        intro h20
        have hval := congrArg Fin.val h20
        simp [c2Index, Certificates.c0Index] at hval)
  rw [Certificates.castIndex_c0'
    data.cert.five_le_k data.cert.five_le_s
    data.baseB.k_le_s] at h
  exact h

private theorem c2_adj_i1
    (data : Certificates.PlusCaseBData G k s) :
    G.Adj (c2 data)
      (data.cert.i
        (Certificates.i1Index' data.cert.five_le_s)) := by
  have h :=
    data.cert.caseB_adj_of_ne data.baseB
      (p := Certificates.c1Index data.cert.five_le_k)
      (r := c2Index data)
      (by
        intro h21
        have hval := congrArg Fin.val h21
        simp [c2Index, Certificates.c1Index] at hval)
  rw [Certificates.castIndex_c1'
    data.cert.five_le_k data.cert.five_le_s
    data.baseB.k_le_s] at h
  exact h

private theorem two_le_of_c2_i_blue
    (data : Certificates.PlusCaseBData G k s)
    (q : Fin (s - 1))
    (hq : ¬G.Adj (c2 data) (data.cert.i q)) :
    2 ≤ q.val := by
  have hq0 : q.val ≠ 0 := by
    intro h0
    have heq :
        q = Certificates.i0Index' data.cert.five_le_s := by
      apply Fin.ext
      simpa using h0
    subst q
    exact hq (c2_adj_i0 data)
  have hq1 : q.val ≠ 1 := by
    intro h1
    have heq :
        q = Certificates.i1Index' data.cert.five_le_s := by
      apply Fin.ext
      simpa using h1
    subst q
    exact hq (c2_adj_i1 data)
  omega

/-- Structural form of the common blue neighborhood in row B-B. -/
private theorem common_blue_c2_xStar_cases
    (data : Certificates.PlusCaseBData G k s)
    {w : Switching.Vertex V k s}
    (hw : w ∈ (BlueGraph data).commonNeighbors
      (Switching.Vertex.core (c2 data)) (xStar data)) :
    w = Switching.Vertex.a
        (Certificates.c0Index data.cert.five_le_k) ∨
      ∃ q : Fin (s - 1), 2 ≤ q.val ∧
        w = Switching.Vertex.y data.cert (some q) := by
  obtain ⟨hc, hx⟩ :=
    (BlueGraph data).mem_commonNeighbors.1 hw
  have hnc : ¬(RedGraph data).Adj
      (Switching.Vertex.core (c2 data)) w :=
    (SimpleGraph.compl_adj _ _ _).1 hc |>.2
  have hnx : ¬(RedGraph data).Adj (xStar data) w :=
    (SimpleGraph.compl_adj _ _ _).1 hx |>.2
  rcases vertex_six_block_cases data.cert w with
    h | h | h | h | h | h
  · obtain ⟨v, rfl⟩ := h
    have hv : v = c2 data := by
      by_contra hne
      exact hnx (((RedGraph data).adj_comm _ _).1
        ((red_adj_core_xStar_iff data v).2 hne))
    subst v
    exact False.elim ((BlueGraph data).loopless.irrefl _ hc)
  · obtain ⟨p, rfl⟩ := h
    have hp :
        p = Certificates.c0Index data.cert.five_le_k := by
      by_contra hne
      exact hnx ((red_adj_xStar_a_iff data p).2 hne)
    exact Or.inl (congrArg Switching.Vertex.a hp)
  · obtain ⟨p, rfl⟩ := h
    have hp :
        p = Certificates.c0Index data.cert.five_le_k := by
      by_contra hne
      exact hnx ((red_adj_xStar_b_iff data p).2 hne)
    subst p
    exact False.elim (hnc ((red_adj_c2_b_iff data
      (Certificates.c0Index data.cert.five_le_k)).2
        (c0_ne_c2 data)))
  · obtain ⟨r, rfl⟩ := h
    have hr : r = none := by
      by_contra hne
      exact hnc ((red_adj_c2_x_iff data r).2 hne)
    subst r
    exact False.elim ((BlueGraph data).loopless.irrefl _ hx)
  · obtain ⟨r, rfl⟩ := h
    cases r with
    | none =>
        exact False.elim
          (hnx ((red_adj_xStar_y_iff data none).2 rfl))
    | some q =>
        right
        refine ⟨q, two_le_of_c2_i_blue data q ?_, rfl⟩
        intro hred
        exact hnc ((red_adj_c2_ySome_iff data q).2 hred)
  · subst w
    exact False.elim (hnx (red_adj_xStar_z data))

/-- Row B-B: deleting the endpoints `c₂,x_*` leaves no blue
`K_(s-1)` in their common neighborhood. -/
theorem blue_common_c2_xStar_cliqueFree
    (data : Certificates.PlusCaseBData G k s) :
    (BlueGraph data).CliqueFreeOn
      ((BlueGraph data).commonNeighbors
        (Switching.Vertex.core (c2 data)) (xStar data))
      (s - 1) := by
  classical
  intro K hKsub hK
  have hCoreZero : Fintype.card (CoreIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro d
    rcases common_blue_c2_xStar_cases data (hKsub d.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
  have hAOne : Fintype.card (AIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    have hp :
        p.1 = Certificates.c0Index data.cert.five_le_k := by
      rcases common_blue_c2_xStar_cases data (hKsub p.2) with h | h
      · exact vertex_a_injective h
      · obtain ⟨r, _, heq⟩ := h
        have := congrArg blockTag heq
        simp at this
    have hq :
        q.1 = Certificates.c0Index data.cert.five_le_k := by
      rcases common_blue_c2_xStar_cases data (hKsub q.2) with h | h
      · exact vertex_a_injective h
      · obtain ⟨r, _, heq⟩ := h
        have := congrArg blockTag heq
        simp at this
    exact hp.trans hq.symm
  have hBZero : Fintype.card (BIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro p
    rcases common_blue_c2_xStar_cases data (hKsub p.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
  have hXZero : Fintype.card (XIn data.cert K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro r
    rcases common_blue_c2_xStar_cases data (hKsub r.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
  have hYIndex :
      ∀ r : YIn data.cert K,
        ∃ q : Fin (s - 1), 2 ≤ q.val ∧ r.1 = some q := by
    intro r
    rcases common_blue_c2_xStar_cases data (hKsub r.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, hq, heq⟩ := h
      exact ⟨q, hq, (vertex_y_injective data.cert heq)⟩
  let qOf (r : YIn data.cert K) : Fin (s - 1) :=
    Classical.choose (hYIndex r)
  have hqOfTwo (r : YIn data.cert K) :
      2 ≤ (qOf r).val :=
    (Classical.choose_spec (hYIndex r)).1
  have hqOfEq (r : YIn data.cert K) :
      r.1 = some (qOf r) :=
    (Classical.choose_spec (hYIndex r)).2
  let f : YIn data.cert K ↪ Fin (s - 3) :=
    { toFun := fun r ↦
        ⟨(qOf r).val - 2, by
          have hlt := (qOf r).isLt
          have htwo := hqOfTwo r
          omega⟩
      inj' := by
        intro r t hrt
        apply Subtype.ext
        rw [hqOfEq r, hqOfEq t]
        congr 1
        apply Fin.ext
        have hval := congrArg Fin.val hrt
        dsimp at hval
        have hr2 := hqOfTwo r
        have ht2 := hqOfTwo t
        omega }
  have hYle : Fintype.card (YIn data.cert K) ≤ s - 3 := by
    simpa using Fintype.card_le_of_injective f f.injective
  have hZZero : Fintype.card (ZIn K) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro z
    rcases common_blue_c2_xStar_cases data (hKsub z.2) with h | h
    · have := congrArg blockTag h
      simp at this
    · obtain ⟨q, _, heq⟩ := h
      have := congrArg blockTag heq
      simp at this
  have hparts := card_eq_six_blocks data.cert K
  have hcard := hK.card_eq
  have hs := data.cert.five_le_s
  omega

private theorem extraBOldGraph_red_cliqueFree
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    (extraBOldGraph data).CliqueFree (k + 1) := by
  classical
  have hk := data.cert.five_le_k
  have hsize : (k - 1) + 2 = k + 1 := by omega
  have hbase :=
    (Switching.switching_extension data.cert hG).1
  have hbase' :
      (Switching.finalGraph data.cert).CliqueFree
        ((k - 1) + 2) := by
    rw [hsize]
    exact hbase
  have hsafe :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        extraBAddedRedRel data u v →
          (extraBOldGraph data).CliqueFreeOn
            ((extraBOldGraph data).commonNeighbors u v)
            (k - 1) := by
    intro u v h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact red_common_i2_a2_cliqueFree data
    · rcases h with ⟨rfl, rfl⟩
      rw [SimpleGraph.commonNeighbors_symm]
      exact red_common_i2_a2_cliqueFree data
  have hclassify :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        (extraBOldGraph data).Adj u v →
          ¬(Switching.finalGraph data.cert).Adj u v →
            extraBAddedRedRel data u v := by
    intro u v hnew hold
    exact classify_extraB_new_red_edge data hnew hold
  have hresult :=
    Switching.cliqueFree_of_new_edges
      (G₀ := Switching.finalGraph data.cert)
      (G₁ := extraBOldGraph data)
      (n := k - 1)
      (Dangerous := extraBAddedRedRel data)
      hbase'
      hclassify
      hsafe
  rw [hsize] at hresult
  exact hresult

private theorem extraBOldGraph_blue_cliqueFree
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    (extraBOldGraph data)ᶜ.CliqueFree (s + 1) := by
  classical
  have hs := data.cert.five_le_s
  have hsize : (s - 1) + 2 = s + 1 := by omega
  have hbase :=
    (Switching.switching_extension data.cert hG).2
  have hbase' :
      (Switching.finalGraph data.cert)ᶜ.CliqueFree
        ((s - 1) + 2) := by
    rw [hsize]
    exact hbase
  have hsafe :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        extraBRemovedRedRel data u v →
          (extraBOldGraph data)ᶜ.CliqueFreeOn
            ((extraBOldGraph data)ᶜ.commonNeighbors u v)
            (s - 1) := by
    intro u v h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact blue_common_c2_xStar_cliqueFree data
    · rcases h with ⟨rfl, rfl⟩
      rw [SimpleGraph.commonNeighbors_symm]
      exact blue_common_c2_xStar_cliqueFree data
  have hclassify :
      ∀ ⦃u v : Switching.Vertex V k s⦄,
        (extraBOldGraph data)ᶜ.Adj u v →
          ¬(Switching.finalGraph data.cert)ᶜ.Adj u v →
            extraBRemovedRedRel data u v := by
    intro u v hnew hold
    exact classify_extraB_new_blue_edge data hnew hold
  have hresult :=
    Switching.cliqueFree_of_new_edges
      (G₀ := (Switching.finalGraph data.cert)ᶜ)
      (G₁ := (extraBOldGraph data)ᶜ)
      (n := s - 1)
      (Dangerous := extraBRemovedRedRel data)
      hbase'
      hclassify
      hsafe
  rw [hsize] at hresult
  exact hresult

/-- The two Type B switches preserve the old graph's
`(k+1,s+1)`-Ramsey freeness. -/
theorem extraBOldGraph_isRamseyFree
    (data : Certificates.PlusCaseBData G k s)
    (hG : IsRamseyFree G k s) :
    IsRamseyFree (extraBOldGraph data) (k + 1) (s + 1) :=
  ⟨extraBOldGraph_red_cliqueFree data hG,
    extraBOldGraph_blue_cliqueFree data hG⟩

end TypeB
end SecondConnector
end RamseyIncrement
