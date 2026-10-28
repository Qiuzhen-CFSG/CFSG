module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest.Coordinates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest.Search

/-!
# The three possible fiber selections

The checked scalar case tree is applied to the actual certified matrix entries.
A binary selection containing fiber zero, with size prime to three and equal
selected representative degrees, has mask 1, 67 or 69. The small final bit tests
identify these masks with the three fiber unions certified by `OrbitCandidates`.
Source context: the ATLAS Held action, GLS3 Table 5.3p and Aschbacher–Smith p.725.
-/

open scoped BigOperators
namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest
public section

@[expose] def maskVector (n : ℕ) (i : Fin 24) : ℕ := if n.testBit i.val then 1 else 0


-- Expand and normalize each row once, keeping the final assembly small.
private theorem sum_weights (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, weights j * b j = 2 + 4 * b 1 + 4 * b 2 + 8 * b 3 + 8 * b 4 + 16 * b 5 + 16 * b 6 + 16 * b 7 + 32 * b 8 + 32 * b 9 + 32 * b 10 + 32 * b 11 + 64 * b 12 + 64 * b 13 + 64 * b 14 + 64 * b 15 + 64 * b 16 + 128 * b 17 + 128 * b 18 + 128 * b 19 + 128 * b 20 + 256 * b 21 + 256 * b 22 + 512 * b 23 := by
  trans 2 * b 0 + (4 * b 1 + (4 * b 2 + (8 * b 3 + (8 * b 4 + (16 * b 5 + (16 * b 6 + (16 * b 7 + (32 * b 8 + (32 * b 9 + (32 * b 10 + (32 * b 11 + (64 * b 12 + (64 * b 13 + (64 * b 14 + (64 * b 15 + (64 * b 16 + (128 * b 17 + (128 * b 18 + (128 * b 19 + (128 * b 20 + (256 * b 21 + (256 * b 22 + (512 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row0 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 0 j * b j = 1 + 4 * b 1 + 4 * b 2 + 16 * b 8 + 16 * b 10 + 64 * b 13 + 64 * b 14 + 256 * b 23 := by
  trans 1 * b 0 + (4 * b 1 + (4 * b 2 + (0 * b 3 + (0 * b 4 + (0 * b 5 + (0 * b 6 + (0 * b 7 + (16 * b 8 + (0 * b 9 + (16 * b 10 + (0 * b 11 + (0 * b 12 + (64 * b 13 + (64 * b 14 + (0 * b 15 + (0 * b 16 + (0 * b 17 + (0 * b 18 + (0 * b 19 + (0 * b 20 + (0 * b 21 + (0 * b 22 + (256 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row1 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 1 j * b j = 2 + 3 * b 1 + 4 * b 3 + 8 * b 7 + 32 * b 8 + 8 * b 10 + 48 * b 14 + 64 * b 19 + 128 * b 22 + 128 * b 23 := by
  trans 2 * b 0 + (3 * b 1 + (0 * b 2 + (4 * b 3 + (0 * b 4 + (0 * b 5 + (0 * b 6 + (8 * b 7 + (32 * b 8 + (0 * b 9 + (8 * b 10 + (0 * b 11 + (0 * b 12 + (0 * b 13 + (48 * b 14 + (0 * b 15 + (0 * b 16 + (0 * b 17 + (0 * b 18 + (64 * b 19 + (0 * b 20 + (0 * b 21 + (128 * b 22 + (128 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row2 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 2 j * b j = 2 + 3 * b 2 + 4 * b 4 + 8 * b 5 + 8 * b 8 + 32 * b 10 + 48 * b 13 + 64 * b 20 + 128 * b 21 + 128 * b 23 := by
  trans 2 * b 0 + (0 * b 1 + (3 * b 2 + (0 * b 3 + (4 * b 4 + (8 * b 5 + (0 * b 6 + (0 * b 7 + (8 * b 8 + (0 * b 9 + (32 * b 10 + (0 * b 11 + (0 * b 12 + (48 * b 13 + (0 * b 14 + (0 * b 15 + (0 * b 16 + (0 * b 17 + (0 * b 18 + (0 * b 19 + (64 * b 20 + (128 * b 21 + (0 * b 22 + (128 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row3 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 3 j * b j = 2 * b 1 + 3 * b 3 + 4 * b 6 + 16 * b 7 + 8 * b 9 + 16 * b 10 + 8 * b 14 + 32 * b 15 + 64 * b 18 + 48 * b 19 + 32 * b 20 + 64 * b 21 + 64 * b 22 + 64 * b 23 := by
  trans 0 * b 0 + (2 * b 1 + (0 * b 2 + (3 * b 3 + (0 * b 4 + (0 * b 5 + (4 * b 6 + (16 * b 7 + (0 * b 8 + (8 * b 9 + (16 * b 10 + (0 * b 11 + (0 * b 12 + (0 * b 13 + (8 * b 14 + (32 * b 15 + (0 * b 16 + (0 * b 17 + (64 * b 18 + (48 * b 19 + (32 * b 20 + (64 * b 21 + (64 * b 22 + (64 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row4 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 4 j * b j = 2 * b 2 + 3 * b 4 + 16 * b 5 + 4 * b 6 + 16 * b 8 + 8 * b 11 + 32 * b 12 + 8 * b 13 + 64 * b 17 + 32 * b 19 + 48 * b 20 + 64 * b 21 + 64 * b 22 + 64 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (2 * b 2 + (0 * b 3 + (3 * b 4 + (16 * b 5 + (4 * b 6 + (0 * b 7 + (16 * b 8 + (0 * b 9 + (0 * b 10 + (8 * b 11 + (32 * b 12 + (8 * b 13 + (0 * b 14 + (0 * b 15 + (0 * b 16 + (64 * b 17 + (0 * b 18 + (32 * b 19 + (48 * b 20 + (64 * b 21 + (64 * b 22 + (64 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row5 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 5 j * b j = 2 * b 2 + 8 * b 4 + 11 * b 5 + 16 * b 8 + 4 * b 9 + 32 * b 12 + 8 * b 13 + 8 * b 16 + 64 * b 17 + 32 * b 19 + 32 * b 20 + 80 * b 21 + 64 * b 22 + 64 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (2 * b 2 + (0 * b 3 + (8 * b 4 + (11 * b 5 + (0 * b 6 + (0 * b 7 + (16 * b 8 + (4 * b 9 + (0 * b 10 + (0 * b 11 + (32 * b 12 + (8 * b 13 + (0 * b 14 + (0 * b 15 + (8 * b 16 + (64 * b 17 + (0 * b 18 + (32 * b 19 + (32 * b 20 + (80 * b 21 + (64 * b 22 + (64 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row6 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 6 j * b j = 2 * b 3 + 2 * b 4 + 5 * b 6 + 16 * b 9 + 16 * b 11 + 24 * b 12 + 16 * b 13 + 16 * b 14 + 24 * b 15 + 32 * b 16 + 32 * b 17 + 32 * b 18 + 24 * b 19 + 24 * b 20 + 32 * b 21 + 32 * b 22 + 96 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (2 * b 3 + (2 * b 4 + (0 * b 5 + (5 * b 6 + (0 * b 7 + (0 * b 8 + (16 * b 9 + (0 * b 10 + (16 * b 11 + (24 * b 12 + (16 * b 13 + (16 * b 14 + (24 * b 15 + (32 * b 16 + (32 * b 17 + (32 * b 18 + (24 * b 19 + (24 * b 20 + (32 * b 21 + (32 * b 22 + (96 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row7 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 7 j * b j = 2 * b 1 + 8 * b 3 + 11 * b 7 + 16 * b 10 + 4 * b 11 + 8 * b 14 + 32 * b 15 + 8 * b 16 + 64 * b 18 + 32 * b 19 + 32 * b 20 + 64 * b 21 + 80 * b 22 + 64 * b 23 := by
  trans 0 * b 0 + (2 * b 1 + (0 * b 2 + (8 * b 3 + (0 * b 4 + (0 * b 5 + (0 * b 6 + (11 * b 7 + (0 * b 8 + (0 * b 9 + (16 * b 10 + (4 * b 11 + (0 * b 12 + (0 * b 13 + (8 * b 14 + (32 * b 15 + (8 * b 16 + (0 * b 17 + (64 * b 18 + (32 * b 19 + (32 * b 20 + (64 * b 21 + (80 * b 22 + (64 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row8 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 8 j * b j = 1 + 4 * b 1 + b 2 + 4 * b 4 + 8 * b 5 + 19 * b 8 + 4 * b 10 + 16 * b 12 + 4 * b 13 + 16 * b 14 + 4 * b 15 + 32 * b 17 + 8 * b 18 + 48 * b 19 + 16 * b 20 + 32 * b 21 + 96 * b 22 + 112 * b 23 := by
  trans 1 * b 0 + (4 * b 1 + (1 * b 2 + (0 * b 3 + (4 * b 4 + (8 * b 5 + (0 * b 6 + (0 * b 7 + (19 * b 8 + (0 * b 9 + (4 * b 10 + (0 * b 11 + (16 * b 12 + (4 * b 13 + (16 * b 14 + (4 * b 15 + (0 * b 16 + (32 * b 17 + (8 * b 18 + (48 * b 19 + (16 * b 20 + (32 * b 21 + (96 * b 22 + (112 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row9 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 9 j * b j = 2 * b 3 + 2 * b 5 + 8 * b 6 + 13 * b 9 + 16 * b 11 + 16 * b 12 + 16 * b 13 + 16 * b 14 + 16 * b 15 + 32 * b 16 + 40 * b 17 + 40 * b 18 + 24 * b 19 + 16 * b 20 + 40 * b 21 + 32 * b 22 + 96 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (2 * b 3 + (0 * b 4 + (2 * b 5 + (8 * b 6 + (0 * b 7 + (0 * b 8 + (13 * b 9 + (0 * b 10 + (16 * b 11 + (16 * b 12 + (16 * b 13 + (16 * b 14 + (16 * b 15 + (32 * b 16 + (40 * b 17 + (40 * b 18 + (24 * b 19 + (16 * b 20 + (40 * b 21 + (32 * b 22 + (96 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row10 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 10 j * b j = 1 + b 1 + 4 * b 2 + 4 * b 3 + 8 * b 7 + 4 * b 8 + 19 * b 10 + 4 * b 12 + 16 * b 13 + 4 * b 14 + 16 * b 15 + 8 * b 17 + 32 * b 18 + 16 * b 19 + 48 * b 20 + 96 * b 21 + 32 * b 22 + 112 * b 23 := by
  trans 1 * b 0 + (1 * b 1 + (4 * b 2 + (4 * b 3 + (0 * b 4 + (0 * b 5 + (0 * b 6 + (8 * b 7 + (4 * b 8 + (0 * b 9 + (19 * b 10 + (0 * b 11 + (4 * b 12 + (16 * b 13 + (4 * b 14 + (16 * b 15 + (0 * b 16 + (8 * b 17 + (32 * b 18 + (16 * b 19 + (48 * b 20 + (96 * b 21 + (32 * b 22 + (112 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row11 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 11 j * b j = 2 * b 4 + 8 * b 6 + 2 * b 7 + 16 * b 9 + 13 * b 11 + 16 * b 12 + 16 * b 13 + 16 * b 14 + 16 * b 15 + 32 * b 16 + 40 * b 17 + 40 * b 18 + 16 * b 19 + 24 * b 20 + 32 * b 21 + 40 * b 22 + 96 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (0 * b 3 + (2 * b 4 + (0 * b 5 + (8 * b 6 + (2 * b 7 + (0 * b 8 + (16 * b 9 + (0 * b 10 + (13 * b 11 + (16 * b 12 + (16 * b 13 + (16 * b 14 + (16 * b 15 + (32 * b 16 + (40 * b 17 + (40 * b 18 + (16 * b 19 + (24 * b 20 + (32 * b 21 + (40 * b 22 + (96 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row12 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 12 j * b j = 4 * b 4 + 8 * b 5 + 6 * b 6 + 8 * b 8 + 8 * b 9 + 2 * b 10 + 8 * b 11 + 21 * b 12 + 8 * b 13 + 8 * b 14 + 12 * b 15 + 20 * b 16 + 52 * b 17 + 16 * b 18 + 24 * b 19 + 28 * b 20 + 56 * b 21 + 48 * b 22 + 88 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (0 * b 3 + (4 * b 4 + (8 * b 5 + (6 * b 6 + (0 * b 7 + (8 * b 8 + (8 * b 9 + (2 * b 10 + (8 * b 11 + (21 * b 12 + (8 * b 13 + (8 * b 14 + (12 * b 15 + (20 * b 16 + (52 * b 17 + (16 * b 18 + (24 * b 19 + (28 * b 20 + (56 * b 21 + (48 * b 22 + (88 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row13 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 13 j * b j = 2 + 3 * b 2 + b 4 + 2 * b 5 + 4 * b 6 + 2 * b 8 + 8 * b 9 + 8 * b 10 + 8 * b 11 + 8 * b 12 + 27 * b 13 + 24 * b 14 + 8 * b 15 + 16 * b 16 + 16 * b 17 + 16 * b 18 + 12 * b 19 + 28 * b 20 + 56 * b 21 + 24 * b 22 + 152 * b 23 := by
  trans 2 * b 0 + (0 * b 1 + (3 * b 2 + (0 * b 3 + (1 * b 4 + (2 * b 5 + (4 * b 6 + (0 * b 7 + (2 * b 8 + (8 * b 9 + (8 * b 10 + (8 * b 11 + (8 * b 12 + (27 * b 13 + (24 * b 14 + (8 * b 15 + (16 * b 16 + (16 * b 17 + (16 * b 18 + (12 * b 19 + (28 * b 20 + (56 * b 21 + (24 * b 22 + (152 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row14 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 14 j * b j = 2 + 3 * b 1 + b 3 + 4 * b 6 + 2 * b 7 + 8 * b 8 + 8 * b 9 + 2 * b 10 + 8 * b 11 + 8 * b 12 + 24 * b 13 + 27 * b 14 + 8 * b 15 + 16 * b 16 + 16 * b 17 + 16 * b 18 + 28 * b 19 + 12 * b 20 + 24 * b 21 + 56 * b 22 + 152 * b 23 := by
  trans 2 * b 0 + (3 * b 1 + (0 * b 2 + (1 * b 3 + (0 * b 4 + (0 * b 5 + (4 * b 6 + (2 * b 7 + (8 * b 8 + (8 * b 9 + (2 * b 10 + (8 * b 11 + (8 * b 12 + (24 * b 13 + (27 * b 14 + (8 * b 15 + (16 * b 16 + (16 * b 17 + (16 * b 18 + (28 * b 19 + (12 * b 20 + (24 * b 21 + (56 * b 22 + (152 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

private theorem sum_row15 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 15 j * b j = 4 * b 3 + 6 * b 6 + 8 * b 7 + 2 * b 8 + 8 * b 9 + 8 * b 10 + 8 * b 11 + 12 * b 12 + 8 * b 13 + 8 * b 14 + 21 * b 15 + 20 * b 16 + 16 * b 17 + 52 * b 18 + 28 * b 19 + 24 * b 20 + 48 * b 21 + 56 * b 22 + 88 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (4 * b 3 + (0 * b 4 + (0 * b 5 + (6 * b 6 + (8 * b 7 + (2 * b 8 + (8 * b 9 + (8 * b 10 + (8 * b 11 + (12 * b 12 + (8 * b 13 + (8 * b 14 + (21 * b 15 + (20 * b 16 + (16 * b 17 + (52 * b 18 + (28 * b 19 + (24 * b 20 + (48 * b 21 + (56 * b 22 + (88 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row16 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 16 j * b j = 2 * b 5 + 8 * b 6 + 2 * b 7 + 16 * b 9 + 16 * b 11 + 20 * b 12 + 16 * b 13 + 16 * b 14 + 20 * b 15 + 29 * b 16 + 36 * b 17 + 36 * b 18 + 16 * b 19 + 16 * b 20 + 40 * b 21 + 40 * b 22 + 96 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (0 * b 3 + (0 * b 4 + (2 * b 5 + (8 * b 6 + (2 * b 7 + (0 * b 8 + (16 * b 9 + (0 * b 10 + (16 * b 11 + (20 * b 12 + (16 * b 13 + (16 * b 14 + (20 * b 15 + (29 * b 16 + (36 * b 17 + (36 * b 18 + (16 * b 19 + (16 * b 20 + (40 * b 21 + (40 * b 22 + (96 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row17 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 17 j * b j = 4 * b 4 + 8 * b 5 + 4 * b 6 + 8 * b 8 + 10 * b 9 + 2 * b 10 + 10 * b 11 + 26 * b 12 + 8 * b 13 + 8 * b 14 + 8 * b 15 + 18 * b 16 + 47 * b 17 + 20 * b 18 + 24 * b 19 + 28 * b 20 + 56 * b 21 + 48 * b 22 + 88 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (0 * b 3 + (4 * b 4 + (8 * b 5 + (4 * b 6 + (0 * b 7 + (8 * b 8 + (10 * b 9 + (2 * b 10 + (10 * b 11 + (26 * b 12 + (8 * b 13 + (8 * b 14 + (8 * b 15 + (18 * b 16 + (47 * b 17 + (20 * b 18 + (24 * b 19 + (28 * b 20 + (56 * b 21 + (48 * b 22 + (88 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row18 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 18 j * b j = 4 * b 3 + 4 * b 6 + 8 * b 7 + 2 * b 8 + 10 * b 9 + 8 * b 10 + 10 * b 11 + 8 * b 12 + 8 * b 13 + 8 * b 14 + 26 * b 15 + 18 * b 16 + 20 * b 17 + 47 * b 18 + 28 * b 19 + 24 * b 20 + 48 * b 21 + 56 * b 22 + 88 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (0 * b 2 + (4 * b 3 + (0 * b 4 + (0 * b 5 + (4 * b 6 + (8 * b 7 + (2 * b 8 + (10 * b 9 + (8 * b 10 + (10 * b 11 + (8 * b 12 + (8 * b 13 + (8 * b 14 + (26 * b 15 + (18 * b 16 + (20 * b 17 + (47 * b 18 + (28 * b 19 + (24 * b 20 + (48 * b 21 + (56 * b 22 + (88 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row19 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 19 j * b j = 2 * b 1 + 3 * b 3 + 2 * b 4 + 4 * b 5 + 3 * b 6 + 4 * b 7 + 12 * b 8 + 6 * b 9 + 4 * b 10 + 4 * b 11 + 12 * b 12 + 6 * b 13 + 14 * b 14 + 14 * b 15 + 8 * b 16 + 24 * b 17 + 28 * b 18 + 33 * b 19 + 22 * b 20 + 44 * b 21 + 76 * b 22 + 100 * b 23 := by
  trans 0 * b 0 + (2 * b 1 + (0 * b 2 + (3 * b 3 + (2 * b 4 + (4 * b 5 + (3 * b 6 + (4 * b 7 + (12 * b 8 + (6 * b 9 + (4 * b 10 + (4 * b 11 + (12 * b 12 + (6 * b 13 + (14 * b 14 + (14 * b 15 + (8 * b 16 + (24 * b 17 + (28 * b 18 + (33 * b 19 + (22 * b 20 + (44 * b 21 + (76 * b 22 + (100 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row20 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 20 j * b j = 2 * b 2 + 2 * b 3 + 3 * b 4 + 4 * b 5 + 3 * b 6 + 4 * b 7 + 4 * b 8 + 4 * b 9 + 12 * b 10 + 6 * b 11 + 14 * b 12 + 14 * b 13 + 6 * b 14 + 12 * b 15 + 8 * b 16 + 28 * b 17 + 24 * b 18 + 22 * b 19 + 33 * b 20 + 76 * b 21 + 44 * b 22 + 100 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (2 * b 2 + (2 * b 3 + (3 * b 4 + (4 * b 5 + (3 * b 6 + (4 * b 7 + (4 * b 8 + (4 * b 9 + (12 * b 10 + (6 * b 11 + (14 * b 12 + (14 * b 13 + (6 * b 14 + (12 * b 15 + (8 * b 16 + (28 * b 17 + (24 * b 18 + (22 * b 19 + (33 * b 20 + (76 * b 21 + (44 * b 22 + (100 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row21 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 21 j * b j = 2 * b 2 + 2 * b 3 + 2 * b 4 + 5 * b 5 + 2 * b 6 + 4 * b 7 + 4 * b 8 + 5 * b 9 + 12 * b 10 + 4 * b 11 + 14 * b 12 + 14 * b 13 + 6 * b 14 + 12 * b 15 + 10 * b 16 + 28 * b 17 + 24 * b 18 + 22 * b 19 + 38 * b 20 + 71 * b 21 + 44 * b 22 + 100 * b 23 := by
  trans 0 * b 0 + (0 * b 1 + (2 * b 2 + (2 * b 3 + (2 * b 4 + (5 * b 5 + (2 * b 6 + (4 * b 7 + (4 * b 8 + (5 * b 9 + (12 * b 10 + (4 * b 11 + (14 * b 12 + (14 * b 13 + (6 * b 14 + (12 * b 15 + (10 * b 16 + (28 * b 17 + (24 * b 18 + (22 * b 19 + (38 * b 20 + (71 * b 21 + (44 * b 22 + (100 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row22 (b : Fin 24 → ℕ) :
    ∑ j : Fin 24, matrix 22 j * b j = 2 * b 1 + 2 * b 3 + 2 * b 4 + 4 * b 5 + 2 * b 6 + 5 * b 7 + 12 * b 8 + 4 * b 9 + 4 * b 10 + 5 * b 11 + 12 * b 12 + 6 * b 13 + 14 * b 14 + 14 * b 15 + 10 * b 16 + 24 * b 17 + 28 * b 18 + 38 * b 19 + 22 * b 20 + 44 * b 21 + 71 * b 22 + 100 * b 23 := by
  trans 0 * b 0 + (2 * b 1 + (0 * b 2 + (2 * b 3 + (2 * b 4 + (4 * b 5 + (2 * b 6 + (5 * b 7 + (12 * b 8 + (4 * b 9 + (4 * b 10 + (5 * b 11 + (12 * b 12 + (6 * b 13 + (14 * b 14 + (14 * b 15 + (10 * b 16 + (24 * b 17 + (28 * b 18 + (38 * b 19 + (22 * b 20 + (44 * b 21 + (71 * b 22 + (100 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [Nat.add_assoc]

private theorem sum_row23 (b : Fin 24 → ℕ) (h0 : b 0 = 1) :
    ∑ j : Fin 24, matrix 23 j * b j = 1 + b 1 + b 2 + b 3 + b 4 + 2 * b 5 + 3 * b 6 + 2 * b 7 + 7 * b 8 + 6 * b 9 + 7 * b 10 + 6 * b 11 + 11 * b 12 + 19 * b 13 + 19 * b 14 + 11 * b 15 + 12 * b 16 + 22 * b 17 + 22 * b 18 + 25 * b 19 + 25 * b 20 + 50 * b 21 + 50 * b 22 + 121 * b 23 := by
  trans 1 * b 0 + (1 * b 1 + (1 * b 2 + (1 * b 3 + (1 * b 4 + (2 * b 5 + (3 * b 6 + (2 * b 7 + (7 * b 8 + (6 * b 9 + (7 * b 10 + (6 * b 11 + (11 * b 12 + (19 * b 13 + (19 * b 14 + (11 * b 15 + (12 * b 16 + (22 * b 17 + (22 * b 18 + (25 * b 19 + (25 * b 20 + (50 * b 21 + (50 * b 22 + (121 * b 23 + (0))))))))))))))))))))))))
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  · simp [h0, Nat.add_assoc]

/-- The representative equations and the three-prime size test have just three solutions. -/
theorem regular_vectors (b : Fin 24 → ℕ) (hb : ∀ i, b i ≤ 1) (h0 : b 0 = 1)
    (hc : ¬ 3 ∣ ∑ i : Fin 24, weights i * b i)
    (hr : ∀ i, b i = 1 → ∑ j : Fin 24, matrix i j * b j =
      ∑ j : Fin 24, matrix 0 j * b j) :
    b = maskVector 1 ∨ b = maskVector 67 ∨ b = maskVector 69 := by
  have hc' : _ := hc
  rw [Nat.dvd_iff_mod_eq_zero, sum_weights b h0] at hc'
  have hh := scalar_candidates (b 1) (hb 1) (b 2) (hb 2) (b 3) (hb 3) (b 4) (hb 4) (b 5) (hb 5) (b 6) (hb 6) (b 7) (hb 7) (b 8) (hb 8) (b 9) (hb 9) (b 10) (hb 10) (b 11) (hb 11) (b 12) (hb 12) (b 13) (hb 13) (b 14) (hb 14) (b 15) (hb 15) (b 16) (hb 16) (b 17) (hb 17) (b 18) (hb 18) (b 19) (hb 19) (b 20) (hb 20) (b 21) (hb 21) (b 22) (hb 22) (b 23) (hb 23) hc'
    (by
      intro hi
      have he := hr 1 hi
      rw [sum_row1 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 2 hi
      rw [sum_row2 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 3 hi
      rw [sum_row3 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 4 hi
      rw [sum_row4 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 5 hi
      rw [sum_row5 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 6 hi
      rw [sum_row6 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 7 hi
      rw [sum_row7 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 8 hi
      rw [sum_row8 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 9 hi
      rw [sum_row9 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 10 hi
      rw [sum_row10 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 11 hi
      rw [sum_row11 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 12 hi
      rw [sum_row12 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 13 hi
      rw [sum_row13 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 14 hi
      rw [sum_row14 b h0, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 15 hi
      rw [sum_row15 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 16 hi
      rw [sum_row16 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 17 hi
      rw [sum_row17 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 18 hi
      rw [sum_row18 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 19 hi
      rw [sum_row19 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 20 hi
      rw [sum_row20 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 21 hi
      rw [sum_row21 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 22 hi
      rw [sum_row22 b, sum_row0 b h0] at he
      exact he)
    (by
      intro hi
      have he := hr 23 hi
      rw [sum_row23 b h0, sum_row0 b h0] at he
      exact he)
  rcases hh with hh | hh | hh
  · rcases hh with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23⟩
    left
    funext i
    fin_cases i
    · exact h0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · exact e21
    · exact e22
    · exact e23
  · rcases hh with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23⟩
    right; left
    funext i
    fin_cases i
    · exact h0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · exact e21
    · exact e22
    · exact e23
  · rcases hh with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23⟩
    right; right
    funext i
    fin_cases i
    · exact h0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · exact e21
    · exact e22
    · exact e23

theorem maskVector_one : ∀ i : Fin 24, maskVector 1 i = 1 ↔ i.val = 0 := by decide +kernel

theorem maskVector_67 : ∀ i : Fin 24,
    maskVector 67 i = 1 ↔ i.val = 0 ∨ i.val = 1 ∨ i.val = 6 := by decide +kernel

theorem maskVector_69 : ∀ i : Fin 24,
    maskVector 69 i = 1 ↔ i.val = 0 ∨ i.val = 2 ∨ i.val = 6 := by decide +kernel

end
end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest
