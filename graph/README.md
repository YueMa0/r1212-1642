# The colouring

r1212_1641.graph has 1641 lines of 1641 characters, 2,694,522 bytes. Character w of line v is 1 if the edge vw is red and 0 if it is blue. The diagonal is 0. SHA-256: see SHA256SUMS.

There is no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1642.

## Vertex order

| Vertices | Role |
|---|---|
| 0–796 | A_x = x of the Mathon graph M(797) |
| 797–1593 | B_x = 797 + x |
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

In M(797), A_x A_y and B_x B_y are red iff x − y is a nonzero square mod 797. A_x B_y is red iff x ≠ y and x − y is not a square. a is red to all of A, b is red to all of B, and every other pair is blue.

The certificates are C = (930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595), a red K₁₀, and I = (1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267), a blue K₁₀.

Rule R* flipped 7 edges of Tatarevic's construction: (1573, 1616) c_2x_0 and (1061, 1626) i_0x_* became blue, and (1597, 1627), (1599, 1627), (1601, 1627), (1603, 1627), (1605, 1627), which are a_1y_0, a_3y_0, a_5y_0, a_7y_0, a_9y_0, became red.

r1212_1641.json records the same data in machine-readable form, including the colour of u towards each special vertex. The construction is described in ../report/r1212_report.md, Sections 1–2 and Appendices A–B.
