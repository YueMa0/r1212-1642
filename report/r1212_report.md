# R(12,12) ≥ 1642: a third connector for Tatarevic's Ramsey increment

Report, 29 October 2026. Yue Ma, with Claude (Claude Opus 5.5, Anthropic); see "How this work was done" in the repository's README.md.

**Status.**
- R(12,12) ≥ 1642 is proved in Lean 4: `r1212_lower_bound : 1642 ≤ ramseyNumber 12 12`. The proof is accepted by the kernel of Lean 4.32.1, by a module-by-module leanchecker replay, and by nanoda, an independently written kernel. Its only axioms are propext, Classical.choice and Quot.sound (Section 6.1).
- Separately, an exhaustive clique search of the 1641-vertex colouring finds no monochromatic K12 (Section 6.2).
- The hand proof in Section 4 has not been checked by another person. The Lean proof does not rely on it.
- The result has not been peer reviewed. Novelty check: Section 8.

## 1. Background and notation

Two-colourings of complete graphs; red = 1, blue = 0. A (k,s)-graph has no red K_k and no blue K_s. If S is a vertex set, "v is red to S" means every edge from v to S is red.

### 1.1 Tatarevic's construction (Type A)

Reference: M. Tatarevic, *A constructive two-parameter Ramsey increment*, arXiv 2608.06531v1 (2026-08-06), Section 4. We restate the Type A branch in the form we implemented. Our implementation reproduces the author's published 1640-vertex colouring exactly, edge for edge, from the same input and certificates (Section 6.5).

**Input.** A (k,s)-graph G on V, with |V| = n. A red K_{k−1} C = (c_0,…,c_{k−2}) and a disjoint blue K_{s−1} I = (i_0,…,i_{s−2}).

Let β(i_q) = {p : c_p i_q is blue}. **Type A** means:
- c_0 i_0 and c_1 i_0 are red;
- P := β(i_0) ≠ ∅, 2 ∈ P ⊆ {2,…,k−2};
- β(i_q) ≠ {1} for every q.

Write T = {q : c_0 i_q red} (so 0 ∈ T), Q = {2,…,k−2} ∖ P, and V° = V ∖ (C ∪ I). In Type A the paper's set E is empty, so its switch (10) does not occur.

**Stage 1 (first lift).** New vertices A = {a_p}, B = {b_p}, p = 0,…,k−2.
- A is a red clique. a_p is red to c_p and blue to the rest of V.
- B is red inside the blocks {b_0, b_1} and {b_2,…,b_{k−2}}, and blue between them.
- b_p is blue to c_p, and colour(b_p, v) = colour(c_p, v) for v ∈ V ∖ {c_p}.
- a_p b_q is blue iff p = q.

Put L = V ∪ A ∪ B and J = (j_0,…,j_{s−1}) = (i_0,…,i_{s−2}, a_0).

**Stage 2 (complementary lift).** New vertices X = {x_r}, Y = {y_r}, r = 0,…,s−1. Write * = s−1.
- X is a blue clique. x_r is blue to j_r and red to the rest of L.
- Y is blue inside the blocks {y_0, y_1} and {y_2,…,y_*}, and red between them.
- y_r is red to j_r, and colour(y_r, v) = colour(j_r, v) for v ∈ L ∖ {j_r}.
- x_r y_t is red iff r = t.

**Stage 3 (connector z).** z copies b_0 on all vertices so far, and z b_0 is red. Then these switches are applied, each with the stated source colour:
- for q ∈ T: a_0 y_q blue→red and b_0 y_q red→blue;
- b_0 y_* blue→red; b_0 b_2 blue→red;
- b_0 x_1, b_0 x_* red→blue;
- z x_r red→blue for every r ∉ {1, *}.

**Stage 4 (connector w).** Switches:
- c_p x_* red→blue for p ∈ P;
- i_0 a_2 blue→red;
- y_0 y_* and y_0 y_2 red→blue.

Then w is added:
- red to C, blue to i_0, and colour(w, v) = colour(i_0, v) for the other v ∈ V;
- blue to a_2, b_0, b_1, b_p (p ∈ P), x_0,…,x_{s−2}, and y_q (q ∉ {0, 2}, q ≤ s−2);
- red to a_p (p ≠ 2), b_q (q ∈ Q), x_*, y_0, y_2, y_*, and z.

The result H⁺ has n + 2k + 2s vertices. **Tatarevic's Theorem 1.1** (Type A branch, valid for k, s ≥ 5; see his Section 4.7) says that H⁺ is a (k+1, s+1)-graph.

### 1.2 The Mathon graph M(q)

For a prime q ≡ 1 (mod 4), let P_q be the Paley graph. M(q) has vertex set A_x, B_x (x ∈ F_q) together with two vertices a and b:
- A and B each induce a copy of P_q;
- a is red to all of A; b is red to all of B;
- A_x B_y is red iff x ≠ y and xy is a non-edge of P_q;
- every other pair is blue.

Neighbourhood lemma (Mathon 1987; Shearer 1986; see Li–Lin 2022, Lemma 2.6), for every vertex v:
- the red graph induced on the red neighbourhood of v is isomorphic to P_q;
- the blue graph induced on the blue neighbourhood of v is isomorphic to P_q plus an isolated vertex. P_q is self-complementary, so the blue graph of P_q is again P_q. For example, the blue neighbourhood of a is B ∪ {b}, and b is blue to no vertex of B.

Hence ω(M(q)) = ω(P_q) + 1 and α(M(q)) = α(P_q) + 1.

Small Ramsey Numbers credits R(11,11) ≥ 1597 to this construction with q = 797. In the Lean proof it is `mathon` (lean/RamseyIncrement/R1212/Mathon.lean). In the graph file the labels are A_x = x, B_x = 797 + x, a = 1594, b = 1595.

## 2. The rule R* and the theorem

**Rule R\*** (Type A). Start from H⁺.

Flip these old edges:
- c_2 x_0 (red→blue);
- i_0 x_* (red→blue);
- a_p y_0 (blue→red) for every odd p ∈ {1,…,k−2}.

That is 2 + ⌊(k−1)/2⌋ edges. None of them is an edge of G.

Add a vertex u:
- red to C, i_0, the a_p with p even, every b_p except b_2, and x_0, x_*, y_*;
- blue to the other vertices of I, the a_p with p odd, b_2, x_1,…,x_{s−2}, y_0,…,y_{s−2}, z and w;
- colour(u, v) = colour(i_0, v) for v ∈ V°.

Call the result O.

**Theorem.** Let k, s ≥ 5, and let G be a (k,s)-graph on n vertices with Type A certificates C, I satisfying
- (P1) P = {2}, that is, i_0 is blue to c_2 and red to every other vertex of C;
- (P2) c_2 is red to at least one of i_2,…,i_{s−2}.

Then O is a (k+1, s+1)-graph on n + 2k + 2s + 1 vertices. Consequently R(k+1, s+1) ≥ n + 2k + 2s + 2.

**Corollary.** R(12,12) ≥ 1642.

Take G = M(797). It is an (11,11)-graph on 1596 vertices: ω(P_797) = α(P_797) = 9 (Section 6.4), then apply the neighbourhood lemma. Appendix A lists certificates in M(797) that satisfy Type A, (P1) and (P2). The Theorem gives a (12,12)-graph on 1596 + 44 + 1 = 1641 vertices. The graph itself is graph/r1212_1641.graph (Appendix B). The corollary is proved in Lean (Section 6.1).

**How to satisfy (P1) and (P2).** These are remarks, not part of the theorem.
- In Tatarevic's orientation lemma, if some column of the incidence matrix has exactly one blue entry and not every row owns such a column, the Type A form puts that column first and its owner at position 2. Then P = {2}.
- The row of c_2 contains a red entry, because otherwise I ∪ {c_2} would be a blue K_s. Type A places no condition on the order of i_1, i_2, …, so a column where c_2 is red can be moved to position ≥ 2.
- In practice, a random search found such certificates immediately in M(797), in the author's 1596-vertex input, and in all 656 McKay (5,5,42)-colourings.

## 3. The colour table of O (Type A with P = {2})

This table is what the proof uses. It was compared with our implementation pair by pair on 320 random Type A cores with P = {2}, for 8 values of (k,s) between (5,5) and (9,9), with no mismatch (Section 6.5). Blocks: B splits as {b_0, b_1} | {b_2,…}, and Y as {y_0, y_1} | {y_2,…,y_*}.

**Fringe vertices against V.**
- a_p is red only to c_p; a_2 is also red to i_0.
- b_p is blue to c_p and copies c_p on the rest of V.
- x_r (r ≤ s−2) is blue only to i_r; x_0 is also blue to c_2 (flip).
- x_* is blue only to c_2 and i_0 (i_0 by the flip).
- y_r (r ≤ s−2) is red to i_r and copies i_r on the rest of V.
- y_* is red only to c_0.
- z is blue to c_0 and copies c_0 on the rest of V.
- w is red to C, blue to i_0, and copies i_0 on the rest of V.
- u is red to C and i_0, blue to I ∖ i_0, and copies i_0 on V°.

In particular, towards a vertex g ∈ V°:
- a's and y_* are blue; x's are red;
- b_p, y_r, z, w, u have the colour of c_p, i_r, c_0, i_0, i_0 respectively.

**Among fringe vertices.**
- A is red; a_p b_q is red iff p ≠ q; A–X is red except a_0 x_* (blue).
- a_p y_r (r ≤ s−2) is blue except a_0 y_q (q ∈ T) and a_p y_0 (p odd), which are red; a_p y_* is red; a_p z is red iff p ≠ 0; a_p w is red iff p ≠ 2.
- B is red inside blocks, blue between blocks, except b_0 b_2 (red); B–X is red except b_0 x_1, b_0 x_* (blue).
- b_0 y_r (r ≤ s−2) is blue; for p ≥ 1, b_p y_r has the colour of c_p i_r; B–y_* is red; b_p z is red iff p ∈ {0,1}; b_p w is red iff p ≥ 3.
- X is blue; x_r y_t is red iff r = t; x_r z is red iff r ∈ {1, *}; x_r w is red iff r = *.
- Y is blue inside blocks and red between them, except y_0 y_2 and y_0 y_* (blue); y_r z is red iff r ∈ T (y_* z is blue); y_r w is red iff r ∈ {0, 2, *}; z w is red.

## 4. Proof of the Theorem

A monochromatic clique of O that contains neither u nor a flipped edge (in its new colour) is a clique of H⁺, so it is small enough by Tatarevic's theorem. It remains to treat:
- (I) cliques through a flipped edge that avoid u;
- (II) red cliques through u;
- (III) blue cliques through u.

### 4.1 Part I: flipped edges

For a flipped edge, let Z be the common neighbourhood of its endpoints in the new colour, without u. A monochromatic K_{s+1} (respectively K_{k+1}) through the edge exists iff Z contains a K_{s−1} (respectively K_{k−1}). We show that Z contains nothing larger than K_{s−2} (respectively K_{k−2}).

**(1) c_2 x_0, now blue.**

x_0 is blue to:
- i_0 and c_2 in V, and no vertex of V° (x is red to V°);
- no vertex of A or B (A–X and B–X are red except a_0 x_*, b_0 x_1, b_0 x_*);
- X ∖ x_0, Y ∖ y_0, z and w.

Intersecting with the blue neighbourhood of c_2 keeps i_0 (2 ∈ P) and x_*. It drops the other x's (c_2 x_r is red) and z, w (both red to c_2). It keeps y_* (red only to c_0), and keeps y_t exactly when c_2 i_t is blue.

So Z = {i_0, x_*, y_*} ∪ Y_b, where Y_b = {y_t : 1 ≤ t ≤ s−2, c_2 i_t blue}.

Colours inside Z:
- i_0 is blue to all of Z;
- x_* y_* is red;
- y_1 is red to y_* and to every y_t with t ≥ 2;
- y_*, y_2,…,y_{s−2} are pairwise blue.

So a blue clique in Z either contains y_1, and then has size ≤ 3, or has size ≤ 2 + |Y_b ∩ {y_2,…,y_{s−2}}| ≤ 2 + (s − 4) = s − 2 by (P2).

**(2) i_0 x_*, now blue.**

x_* is blue to c_2, i_0, a_0, b_0, X ∖ x_* and Y ∖ y_*; it is red to z, w and V°. Intersecting with the blue neighbourhood of i_0:
- b_0 is dropped (b_0 i_0 has the colour of c_0 i_0, red), and so is y_0 (red to i_0);
- among the x's only x_0 remains.

So Z = {c_2, a_0, x_0, y_1,…,y_{s−2}}.

Colours inside Z:
- a_0 x_0 is red; c_2 a_0 and c_2 x_0 are blue;
- c_2 y_t is blue iff c_2 i_t is blue; x_0 y_t is blue;
- y_1 is red to y_{≥2}.

A blue clique in Z contains at most one of a_0, x_0. If it contains y_1, its size is ≤ 3. Otherwise its size is ≤ 2 + (s − 4) when it contains c_2 (by (P2)), and ≤ 1 + (s − 3) when it does not. All of these are ≤ s − 2.

**(3) a_p y_0 for odd p, now red.**

a_p is red to c_p (its only red neighbour in V), A ∖ a_p, B ∖ b_p, all of X, y_0, y_*, z (p ≠ 0) and w (p ≠ 2). Intersecting with the red neighbourhood of y_0:
- c_p stays, since y_0 c_p has the colour of i_0 c_p, which is red because p ∉ P;
- from A, a_0 stays (0 ∈ T) and so do the other odd a's (flips); the even a's with index ≥ 2 go;
- from B, b_q stays iff q ∉ {0, 2, p} (b_0 y_0 is blue; b_2 y_0 has the colour of c_2 i_0, blue);
- from X only x_0 stays; y_* goes (y_0 y_* is blue); z and w stay.

So Z = {c_p, a_0, x_0, z, w} ∪ (A_odd ∖ a_p) ∪ {b_q : q ∉ {0, 2, p}}.

Colours inside Z:
- c_p is blue to every a in Z;
- the a's are pairwise red; a_r b_q is red iff r ≠ q; every a in Z is red to x_0 and w; a_0 z is blue;
- the remaining b's form two blocks, {b_1} and {b_3,…,b_{k−2}} ∖ b_p; b x_0 is red; b_q z is red iff q = 1; b_q w is red iff q ≥ 3;
- x_0 is blue to z and w; z w is red.

Let m = ⌊(k−1)/2⌋, the number of odd indices in {1,…,k−2}. Let K be a red clique in Z and E = K ∩ {x_0, z, w}, so E ⊆ {x_0} or E ⊆ {z, w}.
- (a) c_p ∈ K: K has no a's.
  - With b's from the second block, z ∉ K, so |K| ≤ 1 + (k−4) + 1 = k − 2.
  - With b_1, w ∉ K, so |K| ≤ 3.
  - With no b's, |K| ≤ |{c_p, z, w}| = 3.
- (b) c_p ∉ K and K has b's from the second block: z ∉ K. The index sets of K ∩ A and K ∩ B are disjoint subsets of {0, 1, 3,…,k−2} ∖ {p}, so |K ∩ A| + |K ∩ B| ≤ k − 3 and |K| ≤ k − 2.
- (c) c_p ∉ K and K ∩ B = {b_1} (so p ≠ 1): a_1, w ∉ K. Then |K ∩ A| ≤ m − 1, |E| ≤ 1, and |K| ≤ m + 1.
- (d) c_p ∉ K and K ∩ B = ∅: if a_0 ∈ K, then z ∉ K, so |E| ≤ 1 and |K| ≤ m + 1; otherwise |K ∩ A| ≤ m − 1 and |E| ≤ 2, so again |K| ≤ m + 1.

Since m + 1 ≤ k − 2 for k ≥ 5, every red clique in Z has size ≤ k − 2.

### 4.2 Part II: no red K_k in N_red(u)

N_red(u) = C ∪ {i_0} ∪ G_0 ∪ A_even ∪ B′ ∪ {x_0, x_*, y_*}, where G_0 = {g ∈ V° : g i_0 red} and B′ = B ∖ {b_2}. B′ has blocks {b_0, b_1} and {b_3,…,b_{k−2}}.

Two facts are used repeatedly:
- every vertex of (C ∖ c_2) ∪ G_0 is red to i_0, by (P1);
- after the flips, x_0 and x_* are both blue to c_2 and i_0, and red to the rest of V.

Let K be a red clique in N_red(u), and K_G = K ∩ V.

**II.1: K contains no a and not y_*.** Then K = K_G ∪ K_B ∪ K_X with |K_X| ≤ 1, since x_0 x_* is blue. Define

  π(K) = K_G ∪ {c_q : b_q ∈ K} ∪ ({i_0} if K_X ≠ ∅).

This is a red clique of G with |π(K)| = |K|:
- K_G avoids those c_q (b_q c_q is blue), is red to them (b_q copies c_q), and the c's are pairwise red;
- if K_X ≠ ∅, then K_G avoids c_2 and i_0, so K_G ⊆ (C ∖ c_2) ∪ G_0, which is red to i_0; the c_q (q ≠ 2, as b_2 ∉ B′) are red to i_0; and i_0 ∉ K_G.

Hence |K| ≤ k − 1.

**II.2: K contains some a_p with p even.** Then K_G ⊆ {c_p}, or ⊆ {c_2, i_0} when p = 2. Since c_2 i_0 is blue, |K_G| ≤ 1, and K_G = ∅ when K contains two a's.

Constraints:
- the indices of K_A and K_B are disjoint, and K_B lies in one block of B′;
- x_0 excludes x_* and y_*; x_* excludes a_0 and b_0.

So |K_E| ≤ 2, where K_E = K ∩ {x_0, x_*, y_*}, and |K_E| ≤ 1 when a_0 or b_0 is in K. Let e = ⌊(k−2)/2⌋ + 1, the number of even indices in {0,…,k−2}.

- (a) K_B in the second block: |K_A| + |K_B| ≤ |K_A ∩ {a_0, a_2}| + (k − 4).
  - |K_A| ≥ 2: |K| ≤ 2 + (k−4) + 1 if a_0 ∈ K, and ≤ 1 + (k−4) + 2 otherwise. Both are k − 1.
  - K_A = {a_0}: |K| ≤ 1 + (k−4) + 1 + 1 = k − 1.
  - K_A = {a_2}: c_2 and i_0 are blue to x_0, x_*, y_*, so K_G ≠ ∅ forces K_E = ∅. Either way |K| ≤ k − 1.
  - K_A = {a_p} with p ≥ 4: |K_B| ≤ k − 5, so |K| ≤ 1 + (k−5) + 2 + 1 = k − 1.
- (b) K_B ⊆ {b_0, b_1}.
  - |K_A| ≥ 2: then K_G = ∅. If a_0 ∈ K, then |K_B| ≤ 1 and |K_E| ≤ 1. Otherwise |K_A| ≤ e − 1 and |K_B| + |K_E| ≤ 3. In both cases |K| ≤ e + 2 = ⌊(k−2)/2⌋ + 3 ≤ k − 1.
  - K_A = {a_p}: |K_B| + |K_E| ≤ 3 (b_0 and x_* exclude each other), so |K| ≤ 5. For p = 0 (b_0, x_* excluded) and for p = 2, |K| ≤ 4. For p ≥ 4 we have k ≥ 6, so 5 ≤ k − 1.

**II.3: K contains no a but contains y_*.** Then K_G ⊆ {c_0} (y_* is red only to c_0) and x_0 ∉ K.
- With b's in the second block, |K| ≤ 1 + (k−4) + 2 = k − 1.
- With b's in {b_0, b_1}: b_0 is blue to c_0 and to x_*, so K ⊆ {b_0, b_1, y_*} or K ⊆ {c_0, b_1, x_*, y_*}. Either way |K| ≤ 4.

### 4.3 Part III: no blue K_s in N_blue(u)

N_blue(u) = (I ∖ i_0) ∪ G_1 ∪ A_odd ∪ {b_2} ∪ X_m ∪ Y_l ∪ {z, w}, where:
- G_1 = {g ∈ V° : g i_0 blue};
- X_m = {x_1,…,x_{s−2}};
- Y_l = {y_0,…,y_{s−2}}.

Its part in V is blue to i_0. Let K be a blue clique in N_blue(u), and K_G = K ∩ V.

**III.1: K contains some a_p with p odd.** It contains only one a, because A is red. a_p is red to b_2, X, z, w, y_0 (flip) and y_*. It is blue to y_1,…,y_{s−2} and to V ∖ {c_p} ⊇ K_G. So K = {a_p} ∪ K_G ∪ Y′ with Y′ ⊆ {y_1,…,y_{s−2}}.

Define π(K) = K_G ∪ {i_t : y_t ∈ Y′} ∪ {i_0}. This is a blue clique of G with |π(K)| = |K|:
- g ∈ K_G is blue to y_t, so it is blue to i_t and g ≠ i_t;
- I is blue, and K_G is blue to i_0.

Hence |K| ≤ s − 1.

**III.2: K contains no a but contains some x.** Let X′ = K ∩ X_m ≠ ∅.
- b_2 ∉ K, because B–X is red.
- K_G is either ∅ or {i_r}, and the second case needs X′ = {x_r}.
- Let Y′ = K ∩ Y_l. Its indices are disjoint from those of X′ (x_t y_t is red), and Y′ lies in {y_0, y_1}, in {y_0, y_2}, or in {y_2,…,y_{s−2}}.
- At most one of z, w is in K.

Cases:
- (a) w ∈ K: then y_0, y_2 ∉ K, so |X′| + |Y′| ≤ s − 2.
  - If K_G = ∅, then |K| ≤ s − 1.
  - If K_G = {i_r}, then Y′ ⊆ {y_1} or Y′ ⊆ {y_3,…,y_{s−2}} ∖ y_r, so |Y′| ≤ s − 4 and |K| ≤ s − 1.
- (b) z ∈ K: then x_1, y_0 ∉ K (y_0 z is red because 0 ∈ T). The same counting gives |K| ≤ s − 1.
- (c) Neither z nor w: then |X′| + |Y′| ≤ s − 1.
  - If K_G = ∅, then |K| ≤ s − 1.
  - If K_G = {i_1}, then |Y′| ≤ s − 3, so |K| ≤ s − 1.
  - If K_G = {i_r} with r ≥ 2, then |Y′| ≤ max(2, s − 4), so |K| ≤ 2 + max(2, s − 4) ≤ s − 1.

**III.3: K contains no a and no x.** Then K ⊆ K_G ∪ {b_2} ∪ Y_l ∪ {z, w}. Let I_Y = {i_t : y_t ∈ K}. Define π(K) as follows:
- start with K_G ∪ I_Y, and add c_2 if b_2 ∈ K;
- if w ∈ K, or z, b_2 ∈ K, or neither z nor w is in K, add i_0;
- if z ∈ K and b_2 ∉ K, add c_0.

π(K) is a blue clique of G:
1. g ∈ K_G is blue to i_t (via y_t), to c_2 (via b_2; g ≠ c_2), to c_0 (via z; g ≠ c_0), and to i_0;
2. I is blue;
3. c_2 i_t is blue whenever b_2, y_t ∈ K, because b_2 y_t has the colour of c_2 i_t;
4. c_0 i_t is blue whenever z, y_t ∈ K, because z y_t is blue ⇔ t ∉ T ⇔ c_0 i_t is blue;
5. c_2 i_0 is blue, since 2 ∈ P;
6. c_0 is added only without b_2 and without i_0, so the red pairs c_0 c_2 and c_0 i_0 never both appear.

Sizes:
- no z and no w: |π(K)| = |K| + [y_0 ∉ K];
- w ∈ K: w is replaced by i_0, which is new because y_0 ∉ K (y_0 w is red);
- z, b_2 ∈ K: z is replaced by i_0 (y_0 z is red, so y_0 ∉ K);
- z ∈ K and b_2 ∉ K: z is replaced by c_0.

Thus |π(K)| ≥ |K| in every case, and |K| ≤ s − 1. ∎

**Where the hypotheses are used.**
- (P1) is used in the colour table (w, x_* against B and C), in II ("red to i_0"), and in I(3) (c_p i_0 red).
- (P2) is used only in I(1) and I(2).
- III uses only c_2 i_0 blue and c_0 i_0 red, which hold in every Type A core.

## 5. Why the rule exists: how it was found

These are the computational steps, in order.

1. A non-uniform SAT search for "flip at most d old edges among the certificate and fringe vertices, then add one vertex" on Tatarevic's outputs found:
   - mckay2 (from a McKay (5,5,42)-colouring) needs d = 3; five other McKay inputs need d = 4 (d = 3 is UNSAT, two solvers agree);
   - P101 (k = s = 6) needs d = 4.
2. Two of the McKay solutions and the P101 solution flip the same four role-edges as R*. Written by roles, they extend to all k.
3. A core-level judgement checks "valid for every (k,s)-graph G with this core" by clone projection. Across random cores it found that validity holds exactly when (P1) and (P2) hold:
   - in random samples at (5,5) through (9,9) and (11,11), with no exception;
   - in conditioned samples at (8,8), (9,9), (10,10) and (11,11), all valid.

## 6. Verification

Three checks support the bound, and none of them relies on the hand proof of Section 4: a Lean proof accepted by two independent kernels (6.1), an exhaustive clique search of the colouring (6.2), and a structural check of the colouring by clone projection (6.3).

### 6.1 Lean proof

- **Statement**, in lean/RamseyIncrement/R1212/Main.lean:

  ```lean
  theorem RamseyIncrement.R1212.r1212_lower_bound : 1642 ≤ ramseyNumber 12 12
  ```

  `ramseyNumber k s` is Tatarevic's definition (lean/RamseyIncrement/RamseyNumber.lean): the least n such that every simple graph on `Fin n` contains a k-clique or its complement contains an s-clique. The intermediate result is `r1212_hasRamseyColoring : HasRamseyColoring 1641 12 12`.
- **Contents.**
  - ThirdConnector/ (8 files): rule R* on top of Tatarevic's `plusGraphA` (H⁺), the colour table of Section 3, and `rstar_isRamseyFree`, the Theorem of Section 2 for all k, s ≥ 5.
  - R1212/ (15 files): the Paley graph P_797; a bitset clique search with a proof that it is sound; ω(P_797) ≤ 9; the Mathon graph M(797) and the neighbourhood lemma; the certificates of Appendix A; the final theorem.
- **ω(P_797) ≤ 9.** The map x ↦ (x − u)/(v − u) sends a clique through u and v to a clique through 0 and 1, so it is enough that the common neighbourhood of 0 and 1 (198 vertices) has no K8. The kernel runs the verified search on this graph, split into 148 top-level branches (`decide +kernel`). The data tables come from r1212_corollary/gen/gen_h01.py, but Lean checks them against Euler's criterion, so the result does not depend on the generator.
- **M(797).** The neighbourhood lemma is proved by explicit maps, without computation. Blue cliques are mapped by twice the red maps. Since x ↦ 2x maps P_797 onto its complement, only ω(P_797) ≤ 9 is needed.
- **Checks.**
  - `#print axioms r1212_lower_bound`: propext, Classical.choice, Quot.sound.
  - The new files contain no sorry, admit, native_decide, axiom, unsafe, implemented_by, extern or opaque.
  - leanchecker accepts the 23 new modules and the 43 modules of Tatarevic's library, replayed one module at a time. The proof uses constants from 31 of the 43, namely the Type A branch of Tatarevic's theorem.
  - nanoda (written in Rust, big integers by num-bigint rather than GMP; commit d0a02cc) checks an export of the theorem and all its dependencies made with lean4export: 31,106 declarations, no errors. It prints the theorem and the definitions in its statement, and they are as stated above.
  - Control: changing the single literal 398 (the exponent in Euler's criterion) in an export of `rowH_spec` makes nanoda reject it.
  - Positive control: run by the compiler, the same search reports that the 198-vertex graph does contain a K7, as ω(P_797) = 9 requires.
- **Cost.** Each of the eight branch modules takes about 80–110 s and 4–7 GB in the Lean kernel. On a 16 GB machine they must be built one at a time (lean/audit/build_r1212.sh). nanoda needs about 11 GB and 5 minutes with 2 threads.

### 6.2 Exhaustive clique search

- verify/bruteforce_kclique.c decides, for each vertex v and colour c, whether the later vertices joined to v in colour c contain a K11 of colour c. It is an exact bitset branch and bound and uses no structure of the graph.
- On graph/r1212_1641.graph all 3,282 tasks return "none": there is no monochromatic K12. The search visited 1.888 × 10^11 nodes in 15.28 CPU-hours (8 threads on an Apple M4, 1 h 55 min). Output: verify/results/bruteforce_r1212_1641.jsonl.
- The program agrees with networkx on random colourings, and it finds a K12 when one flip of R* is undone.
- Second check (verify/second_check/):
  - an independent review of the program, by a separate Claude agent that was given only the program, the colouring and the outputs, found no defect that could affect this result, and five robustness issues that this run did not trigger (verify/README.md);
  - the reviewer wrote three implementations that share no code with the program. They agree with each other and with networkx on 3,784 synthetic tasks. On the real graph, two of them return "none" on the 682 tasks with v ≥ 1300; the third returns "none" on the 1,482 tasks with v ≥ 900 and on four large tasks including the largest, with exactly the same node counts as the original run;
  - K12s planted into the largest subproblems are found;
  - the first 1596 vertices of the file coincide with the Lean definition `mathon`, evaluated entry by entry.
- The 1,796 tasks with v < 900 (99.4% of the search) were run only once, by the original program. Ruling out a transient hardware fault in that run would need a complete rerun, about 15 CPU-hours.

### 6.3 Clone projection; rebuilding from this report

- verify/check_projection.py: on the 1576 vertices of M(797) outside C ∪ I, each of the 45 new vertices is constant or a copy of a certificate vertex. So every monochromatic clique projects onto a clique of M(797) together with a set of the 65 special vertices. All 8,773 red and 7,998 blue maximal cliques among the special vertices pass. Undoing any class of flips produces a genuine K12 (negative controls).
- verify/rebuild_from_report.py builds the colouring from Sections 1.1, 1.2, 2 and Appendices A and B of this report alone. Its output is byte-identical to graph/r1212_1641.graph.

### 6.4 ω(P_797) = α(P_797) = 9

Paley graphs are arc-transitive (x ↦ ax + b with a a nonzero square). So a red K10 exists iff the common neighbourhood of 0 and 1 (198 vertices) contains a red K8. For the complement, use 0 and the non-square 2 (198 vertices).

Both searches were exhaustive, with no K8, and were repeated by independent implementations. This agrees with the literature: Shearer 1986, Table I (p. 303), lists p = 797 as the largest prime with clique number 9 below 3000; Mathon 1987, Table I (p. 124), gives α_797 = 9. Witness 9-cliques:
- red: {0, 1, 784, 788, 730, 773, 695, 643, 94};
- blue: {0, 2, 768, 794, 760, 765, 626, 480, 478}.

The Lean proof uses only the upper bound ω(P_797) ≤ 9.

### 6.5 Evidence used while finding the rule

These checks were made with research scripts that are not part of this repository. The results above do not depend on them.
- Our implementation of Tatarevic's construction agrees with the paper's branch statistics on all 35,714 admissible 4×4 incidence matrices. From the author's input and certificates (C = {1,2,0,3,…,9}, I = {10,11,20,21,35,78,165,205,259,797}, Type A with P = {2,6,9}, applied to the complement) it rebuilds the author's 1640-vertex colouring with 0 differing pairs.
- The colour table of Section 3 matches the implementation pair by pair, including the colours towards V°, on 320 random Type A cores with P = {2}, for (k,s) from (5,5) to (9,9).
- Each case of Section 4 was checked on 300 random (k,s)-graphs containing a core with (P1), (P2), 50 each for (5,5), (5,6), (6,6), (7,7), (8,8), (9,9), with 0 failures:

| Case | Cliques checked |
|---|---|
| II.1 | 951,247 |
| II.2 | 133,200 |
| II.3 | 14,600 |
| III.1 | 809,873 |
| III.2 | 286,121 |
| III.3 | 587,144 |
| Flipped-edge neighbourhoods | 1,400 |

- Planted tests (random G containing a core with (P1), (P2); every K_{k+1} and K_{s+1} of the output listed): all valid at (5,5) 100/100, (6,6) 60/60, (7,7) 40/40, (8,8) 40/40, (11,11) 40/40. All 656 McKay (5,5,42) instances (328 colourings and their complements) have certificates with (P1), (P2), and all 656 outputs are (6,6)-graphs.

## 7. Files

| Item | Path | SHA-256 |
|---|---|---|
| The colouring: 1641 lines of 1641 characters, 2,694,522 bytes | graph/r1212_1641.graph | 9550a1745bfa46e595b24bc44f279aed86199c72d8f6e5483080296055c8e485 |
| Output of the exhaustive search | verify/results/bruteforce_r1212_1641.jsonl | b0211fae550183e126c179cfa80f6bab29831b4db97c4addee01a56b7c9780e7 |
| New Lean sources | lean/RamseyIncrement/ThirdConnector/, lean/RamseyIncrement/R1212/ | lean/audit/sources.sha256 |

The commands that reproduce each check are in README.md.

## 8. Novelty check (29 October 2026)

Two literature searches were made on 29 October 2026, the second after the Lean proof was complete. Neither found a bound R(12,12) ≥ 1642, an increment of the form 2k + 2s + 1, or an improvement of R(11,11) ≥ 1597.
- arXiv 2608.06531 has only v1 (6 August 2026). The last commit of its repository is from 10 August 2026, and the author's latest blog post (28 July 2026) states 1641.
- The latest revision of Small Ramsey Numbers (24 April 2026) lists R(12,12) ≥ 1640.
- In 2026 several computer and AI-assisted searches improved other classical Ramsey numbers (for example arXiv 2603.09172 and arXiv 2610.12122). All of them concern off-diagonal numbers.
- Searches cannot cover unpublished or very recent work.

## 9. What is not established

1. **The definitions in the statement.** The Lean theorem uses Tatarevic's `ramseyNumber`, `HasRamseyColoring` and `IsRamseyFree`, and Mathlib's `SimpleGraph.CliqueFree`. nanoda prints them (lean/audit/nanoda/logs/full.log). They express the usual Ramsey number, but nobody else has reviewed them.
2. **The export.** The nanoda check assumes that lean4export exported the proof faithfully.
3. **The hand proof of Section 4** has not been checked by another person. The Lean proof and the computer checks do not rely on it.
4. **Peer review.** None yet.

## Appendix A. The certificates in M(797)

Labels: A_x = x and B_x = 797 + x for x ∈ F_797, a = 1594, b = 1595. In B, B_x B_y is red iff x − y is a nonzero square mod 797. b is red to all of B. a is blue to all of B and to b.

- C (red K10, in construction order c_0,…,c_9): B133, B129, B776, B541, B682, B686, B695, B785, B789, b. Raw indices: 930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595.
- I (blue K10, i_0,…,i_9): B264, B791, B779, B752, B757, a, B675, B760, B282, B470. Raw indices: 1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267.
- Checks:
  - all differences among the nine B-labels of C are squares;
  - all differences among the nine B-labels of I are non-squares.

Incidence matrix (rows c_p, columns i_q; R = red, . = blue):

```
c0  B133  R.R...RR.R
c1  B129  RR..R..RR.
c2  B776  .R.R...RR.
c3  B541  RRR.R...RR
c4  B682  RR.....RR.
c5  B686  R.RRR.RR.R
c6  B695  RRRRR...RR
c7  B785  RRR...RRRR
c8  B789  R.R.......
c9     b  RRRRR.RRRR
```

Reading the matrix:
- Column i_0 has its only blue entry in row c_2, so P = {2}; c_0 and c_1 are red to i_0.
- No column has blue set {1}, so the matrix is Type A.
- Row c_2 is red at i_3, i_7 and i_8, which gives (P2).

## Appendix B. Layout of the graph file

The file is 1641 lines of 1641 characters; character v of line u is 1 iff uv is red. The colours are as built, with no complement.

| Vertices | Role |
|---|---|
| 0–796 | A_x |
| 797–1593 | B_x |
| 1594 | a |
| 1595 | b |
| 1596–1605 | a_0,…,a_9 |
| 1606–1615 | b_0,…,b_9 |
| 1616–1625 | x_0,…,x_9 |
| 1626 | x_* |
| 1627–1636 | y_0,…,y_9 |
| 1637 | y_* |
| 1638 | z |
| 1639 | w |
| 1640 | u |

The 7 flipped edges are (1573, 1616) c_2x_0, (1061, 1626) i_0x_*, and (1597, 1627), (1599, 1627), (1601, 1627), (1603, 1627), (1605, 1627), which are a_1y_0, a_3y_0, a_5y_0, a_7y_0, a_9y_0.

## References

- M. Tatarevic, A constructive two-parameter Ramsey increment, arXiv 2608.06531v1, 2026; repository github.com/milostatarevic/ramsey-increment-theorem (commit 36c15ec).
- X. Xu, Z. Shao, S. P. Radziszowski, More constructive lower bounds on classical Ramsey numbers, SIAM J. Discrete Math. 25 (2011) 394–400.
- R. Mathon, Lower bounds for Ramsey numbers and association schemes, J. Combin. Theory Ser. B 42 (1987) 122–127.
- J. B. Shearer, Lower bounds for small diagonal Ramsey numbers, J. Combin. Theory Ser. A 42 (1986) 302–304.
- Y. Li, Q. Lin, Elementary Methods of Graph Ramsey Theory, Springer, 2022, Section 2.5.
- S. P. Radziszowski, Small Ramsey numbers, Electron. J. Combin. Dynamic Survey DS1, revision 18, 2026-04-24.
- A. Nagda, P. Raghavan, A. Thakurta, Reinforced generation of combinatorial structures: Ramsey numbers, arXiv 2603.09172, 2026.
- F. Cremer, Lower bounds for Ramsey numbers: R(6,8) ≥ 135 and R(8,10) ≥ 345, arXiv 2610.12122, 2026.
- Lean 4 (v4.32.1) and Mathlib (tag v4.32.1); lean4export, github.com/leanprover/lean4export (tag v4.32.2); nanoda_lib, github.com/ammkrn/nanoda_lib (commit d0a02cc).
