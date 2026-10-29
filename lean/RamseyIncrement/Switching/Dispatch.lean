/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Switching.Assembly

/-!
# Dispatching the explicit switching rows

The changed-edge graphs store each switch without a preferred orientation.
This module performs the finite dispatch from those symmetric edge
classifications to the four red and six blue row statements.
-/

namespace RamseyIncrement
namespace Switching

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k s : ℕ}

/-- If every displayed row in the switching table is safe in its canonical
orientation, then the final graph is Ramsey-free. -/
theorem final_isRamseyFree_of_explicit_rows
    (cert : Certificates.OrderedCertificates G k s)
    (hG : IsRamseyFree G k s)
    (hR1 :
      (finalGraph cert).CliqueFreeOn
        ((finalGraph cert).commonNeighbors
          (Vertex.b (Vertex.c0 cert)) Vertex.z) (k - 1))
    (hR2 :
      ∀ q ∈ cert.T,
        (finalGraph cert).CliqueFreeOn
          ((finalGraph cert).commonNeighbors
            (Vertex.a (Vertex.c0 cert)) (Vertex.y cert (some q)))
          (k - 1))
    (hR3 :
      (finalGraph cert).CliqueFreeOn
        ((finalGraph cert).commonNeighbors
          (Vertex.b (Vertex.c0 cert)) (Vertex.y cert none)) (k - 1))
    (hR4 :
      (finalGraph cert).CliqueFreeOn
        ((finalGraph cert).commonNeighbors
          (Vertex.b (Vertex.c0 cert)) (Vertex.b (Vertex.c2 cert)))
        (k - 1))
    (hB1 :
      ∀ q ∈ cert.T,
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.b (Vertex.c0 cert)) (Vertex.y cert (some q)))
          (s - 1))
    (hB2 :
      (finalGraph cert)ᶜ.CliqueFreeOn
        ((finalGraph cert)ᶜ.commonNeighbors
          (Vertex.b (Vertex.c0 cert))
          (Vertex.x cert (some (Vertex.i1 cert)))) (s - 1))
    (hB3 :
      (finalGraph cert)ᶜ.CliqueFreeOn
        ((finalGraph cert)ᶜ.commonNeighbors
          (Vertex.b (Vertex.c0 cert)) (Vertex.x cert none)) (s - 1))
    (hB4 :
      ∀ q, q ≠ Vertex.i1 cert →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            Vertex.z (Vertex.x cert (some q))) (s - 1))
    (hB5 :
      ∀ q ∈ cert.E,
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.a (Vertex.c0 cert)) (Vertex.x cert (some q)))
          (s - 1))
    (hB6star :
      cert.E.Nonempty →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.y cert (some (Vertex.i1 cert)))
            (Vertex.y cert none)) (s - 1))
    (hB6large :
      ∀ q ∈ cert.E, 2 ≤ q.val →
        (finalGraph cert)ᶜ.CliqueFreeOn
          ((finalGraph cert)ᶜ.commonNeighbors
            (Vertex.y cert (some (Vertex.i1 cert)))
            (Vertex.y cert (some q))) (s - 1)) :
    IsRamseyFree (finalGraph cert) (k + 1) (s + 1) := by
  classical
  apply final_isRamseyFree_of_row_safety cert hG hR1
  · intro u v huv
    rcases (addedRedGraph_adj_iff cert u v).1 huv with
      ⟨q, hqT, h | h⟩ | h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hR2 q hqT
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert).commonNeighbors_symm]
      exact hR2 q hqT
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact hR3
      · rcases h with ⟨rfl, rfl⟩
        rw [(finalGraph cert).commonNeighbors_symm]
        exact hR3
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact hR4
      · rcases h with ⟨rfl, rfl⟩
        rw [(finalGraph cert).commonNeighbors_symm]
        exact hR4
  · intro u v huv
    rcases (removedRedGraph_adj_iff cert u v).1 huv with
      ⟨q, hqT, h | h⟩ | h | h | ⟨q, hq1, h | h⟩ |
        ⟨q, hqE, h | h⟩ | ⟨hE, h | h⟩ |
        ⟨q, hqE, hq2, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      exact hB1 q hqT
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
      exact hB1 q hqT
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact hB2
      · rcases h with ⟨rfl, rfl⟩
        rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
        exact hB2
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact hB3
      · rcases h with ⟨rfl, rfl⟩
        rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
        exact hB3
    · rcases h with ⟨rfl, rfl⟩
      exact hB4 q hq1
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
      exact hB4 q hq1
    · rcases h with ⟨rfl, rfl⟩
      exact hB5 q hqE
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
      exact hB5 q hqE
    · rcases h with ⟨rfl, rfl⟩
      exact hB6star hE
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
      exact hB6star hE
    · rcases h with ⟨rfl, rfl⟩
      exact hB6large q hqE hq2
    · rcases h with ⟨rfl, rfl⟩
      rw [(finalGraph cert)ᶜ.commonNeighbors_symm]
      exact hB6large q hqE hq2

end Switching
end RamseyIncrement
