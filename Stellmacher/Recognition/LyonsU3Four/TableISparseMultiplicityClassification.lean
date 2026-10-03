module

public import Stellmacher.Recognition.LyonsU3Four.TableISparseRowSupport
public import Mathlib.Tactic.ClearExcept

/-!
# Multiplicities in the sparse branch of Lyons's Table I

The 85 candidate rows form 31 rotation orbits. Seven entries of the Gram
matrix give the orbit equations below. Positive-coefficient combinations and
principal positivity eliminate 22 orbit multiplicities.

For the remaining nine, put `A = n 5`, `B = n 15`, `C = n 34`, and `t = n 58`.
The equations imply `A + B + C = 1` and `n 57 + 2*t = 2*(A+B)`; all remaining
multiplicities are determined linearly. Thus there are five solutions, the
multiplicity vectors of M, N, P, Q, and R. Catalogue injectivity and coverage of
each printed matrix extend the comparison to every row, including rows outside
the catalogue. Every finite coefficient and count comparison is kernel checked.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Case 6(a),(b), and Table I.
-/

@[expose] public section
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

namespace Stellmacher.Recognition.LyonsU3Four.TableISparseRows
/-- Orbit number of each catalogue entry, in order of its first occurrence. -/
private def orbitIndex : Fin 85 → Fin 31 := ![0, 0, 0, 0, 1, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 6, 7, 8, 8, 8, 8, 9,
  9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 12, 13, 14, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18,
  18, 18, 19, 19, 19, 19, 20, 21, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27,
  27, 27, 28, 29, 30, 30, 30, 30]
private def representative : Fin 31 → Fin 85 := ![0, 4, 5, 6, 10, 14, 15, 16, 17, 21, 25, 29, 33, 34, 35, 36,
  40, 44, 48, 52, 56, 57, 58, 59, 63, 67, 71, 75, 79, 80, 81]

private theorem normalize {n : Fin 85 → ℕ} (h : MultiplicityConditions n) :
    n = fun a => n (representative (orbitIndex a)) := by
  funext a
  fin_cases a
  · exact rfl
  · exact (h.galois 1).symm
  · exact ((h.galois 2).symm).trans (h.galois 1).symm
  · exact (((h.galois 3).symm).trans (h.galois 2).symm).trans (h.galois 1).symm
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (h.galois 7).symm
  · exact ((h.galois 8).symm).trans (h.galois 7).symm
  · exact (((h.galois 9).symm).trans (h.galois 8).symm).trans (h.galois 7).symm
  · exact rfl
  · exact (h.galois 11).symm
  · exact ((h.galois 12).symm).trans (h.galois 11).symm
  · exact (((h.galois 13).symm).trans (h.galois 12).symm).trans (h.galois 11).symm
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (((h.galois 18).symm).trans (h.galois 19).symm).trans (h.galois 20).symm
  · exact ((h.galois 19).symm).trans (h.galois 20).symm
  · exact (h.galois 20).symm
  · exact rfl
  · exact (h.galois 22).symm
  · exact ((h.galois 23).symm).trans (h.galois 22).symm
  · exact (((h.galois 24).symm).trans (h.galois 23).symm).trans (h.galois 22).symm
  · exact rfl
  · exact (h.galois 26).symm
  · exact ((h.galois 27).symm).trans (h.galois 26).symm
  · exact (((h.galois 28).symm).trans (h.galois 27).symm).trans (h.galois 26).symm
  · exact rfl
  · exact (h.galois 30).symm
  · exact ((h.galois 31).symm).trans (h.galois 30).symm
  · exact (((h.galois 32).symm).trans (h.galois 31).symm).trans (h.galois 30).symm
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (((h.galois 37).symm).trans (h.galois 38).symm).trans (h.galois 39).symm
  · exact ((h.galois 38).symm).trans (h.galois 39).symm
  · exact (h.galois 39).symm
  · exact rfl
  · exact (((h.galois 41).symm).trans (h.galois 42).symm).trans (h.galois 43).symm
  · exact ((h.galois 42).symm).trans (h.galois 43).symm
  · exact (h.galois 43).symm
  · exact rfl
  · exact (h.galois 45).symm
  · exact ((h.galois 46).symm).trans (h.galois 45).symm
  · exact (((h.galois 47).symm).trans (h.galois 46).symm).trans (h.galois 45).symm
  · exact rfl
  · exact (h.galois 49).symm
  · exact ((h.galois 50).symm).trans (h.galois 49).symm
  · exact (((h.galois 51).symm).trans (h.galois 50).symm).trans (h.galois 49).symm
  · exact rfl
  · exact (h.galois 53).symm
  · exact ((h.galois 54).symm).trans (h.galois 53).symm
  · exact (((h.galois 55).symm).trans (h.galois 54).symm).trans (h.galois 53).symm
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (((h.galois 60).symm).trans (h.galois 61).symm).trans (h.galois 62).symm
  · exact ((h.galois 61).symm).trans (h.galois 62).symm
  · exact (h.galois 62).symm
  · exact rfl
  · exact (((h.galois 64).symm).trans (h.galois 65).symm).trans (h.galois 66).symm
  · exact ((h.galois 65).symm).trans (h.galois 66).symm
  · exact (h.galois 66).symm
  · exact rfl
  · exact (((h.galois 68).symm).trans (h.galois 69).symm).trans (h.galois 70).symm
  · exact ((h.galois 69).symm).trans (h.galois 70).symm
  · exact (h.galois 70).symm
  · exact rfl
  · exact (h.galois 72).symm
  · exact ((h.galois 73).symm).trans (h.galois 72).symm
  · exact (((h.galois 74).symm).trans (h.galois 73).symm).trans (h.galois 72).symm
  · exact rfl
  · exact (h.galois 76).symm
  · exact ((h.galois 77).symm).trans (h.galois 76).symm
  · exact (((h.galois 78).symm).trans (h.galois 77).symm).trans (h.galois 76).symm
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (((h.galois 82).symm).trans (h.galois 83).symm).trans (h.galois 84).symm
  · exact ((h.galois 83).symm).trans (h.galois 84).symm
  · exact (h.galois 84).symm

/-- Orbit contributions to the seven independent Gram entries used here. -/
private structure Equations (n : Fin 85 → ℕ) : Prop where
  e00 : (36) * (n 0 : ℤ) + (9) * (n 4 : ℤ) + (9) * (n 5 : ℤ) + (16) * (n 6 : ℤ) + (16) * (n 10 : ℤ) + (4) * (n
    14 : ℤ) + (4) * (n 15 : ℤ) + (1) * (n 16 : ℤ) + (4) * (n 17 : ℤ) + (4) * (n 21 : ℤ) + (4) * (n 25 : ℤ) + (4)
    * (n 29 : ℤ) + (1) * (n 33 : ℤ) + (1) * (n 34 : ℤ) + (4) * (n 48 : ℤ) + (4) * (n 52 : ℤ) + (1) * (n 56 : ℤ)
    + (1) * (n 57 : ℤ) + (1) * (n 58 : ℤ) + (4) * (n 59 : ℤ) + (4) * (n 63 : ℤ) + (4) * (n 67 : ℤ) + (16) * (n
    71 : ℤ) + (16) * (n 75 : ℤ) + (4) * (n 79 : ℤ) + (4) * (n 80 : ℤ) + (36) * (n 81 : ℤ) = 16
  e11 : (1) * (n 4 : ℤ) + (1) * (n 5 : ℤ) + (4) * (n 6 : ℤ) + (4) * (n 10 : ℤ) + (4) * (n 14 : ℤ) + (4) * (n 15
    : ℤ) + (1) * (n 16 : ℤ) + (16) * (n 21 : ℤ) + (16) * (n 25 : ℤ) + (16) * (n 29 : ℤ) + (9) * (n 33 : ℤ) + (9)
    * (n 34 : ℤ) + (4) * (n 36 : ℤ) + (4) * (n 40 : ℤ) + (36) * (n 44 : ℤ) + (1) * (n 56 : ℤ) + (1) * (n 57 : ℤ)
    + (1) * (n 58 : ℤ) + (16) * (n 59 : ℤ) + (16) * (n 63 : ℤ) + (16) * (n 67 : ℤ) + (4) * (n 71 : ℤ) + (4) * (n
    75 : ℤ) + (4) * (n 79 : ℤ) + (4) * (n 80 : ℤ) = 16
  e22 : (1) * (n 0 : ℤ) + (1) * (n 5 : ℤ) + (1) * (n 6 : ℤ) + (7) * (n 10 : ℤ) + (1) * (n 14 : ℤ) + (4) * (n 15
    : ℤ) + (1) * (n 16 : ℤ) + (3) * (n 17 : ℤ) + (1) * (n 21 : ℤ) + (7) * (n 25 : ℤ) + (21) * (n 29 : ℤ) + (4) *
    (n 33 : ℤ) + (9) * (n 34 : ℤ) + (1) * (n 35 : ℤ) + (3) * (n 36 : ℤ) + (13) * (n 40 : ℤ) + (21) * (n 44 : ℤ)
    + (1) * (n 48 : ℤ) + (7) * (n 52 : ℤ) + (1) * (n 57 : ℤ) + (4) * (n 58 : ℤ) + (3) * (n 59 : ℤ) + (13) * (n
    63 : ℤ) + (31) * (n 67 : ℤ) + (1) * (n 71 : ℤ) + (7) * (n 75 : ℤ) + (1) * (n 79 : ℤ) + (4) * (n 80 : ℤ) +
    (3) * (n 81 : ℤ) = 16
  e01 : (-3) * (n 4 : ℤ) + (-3) * (n 5 : ℤ) + (-8) * (n 6 : ℤ) + (-8) * (n 10 : ℤ) + (-4) * (n 14 : ℤ) + (-4) *
    (n 15 : ℤ) + (1) * (n 16 : ℤ) + (-8) * (n 21 : ℤ) + (-8) * (n 25 : ℤ) + (-8) * (n 29 : ℤ) + (-3) * (n 33 :
    ℤ) + (-3) * (n 34 : ℤ) + (1) * (n 56 : ℤ) + (1) * (n 57 : ℤ) + (1) * (n 58 : ℤ) + (8) * (n 59 : ℤ) + (8) *
    (n 63 : ℤ) + (8) * (n 67 : ℤ) + (8) * (n 71 : ℤ) + (8) * (n 75 : ℤ) + (4) * (n 79 : ℤ) + (4) * (n 80 : ℤ) =
    0
  e02 : (-3) * (n 0 : ℤ) + (-3) * (n 5 : ℤ) + (-2) * (n 6 : ℤ) + (-10) * (n 10 : ℤ) + (-2) * (n 14 : ℤ) + (-4) *
    (n 15 : ℤ) + (-1) * (n 16 : ℤ) + (-3) * (n 17 : ℤ) + (-1) * (n 21 : ℤ) + (-5) * (n 25 : ℤ) + (-9) * (n 29 :
    ℤ) + (-2) * (n 33 : ℤ) + (-3) * (n 34 : ℤ) + (1) * (n 48 : ℤ) + (5) * (n 52 : ℤ) + (1) * (n 57 : ℤ) + (2) *
    (n 58 : ℤ) + (3) * (n 59 : ℤ) + (7) * (n 63 : ℤ) + (11) * (n 67 : ℤ) + (2) * (n 71 : ℤ) + (10) * (n 75 : ℤ)
    + (2) * (n 79 : ℤ) + (4) * (n 80 : ℤ) + (9) * (n 81 : ℤ) = 0
  e12 : (1) * (n 5 : ℤ) + (1) * (n 6 : ℤ) + (5) * (n 10 : ℤ) + (2) * (n 14 : ℤ) + (4) * (n 15 : ℤ) + (-1) * (n
    16 : ℤ) + (2) * (n 21 : ℤ) + (10) * (n 25 : ℤ) + (18) * (n 29 : ℤ) + (6) * (n 33 : ℤ) + (9) * (n 34 : ℤ) +
    (3) * (n 36 : ℤ) + (7) * (n 40 : ℤ) + (27) * (n 44 : ℤ) + (1) * (n 57 : ℤ) + (2) * (n 58 : ℤ) + (6) * (n 59
    : ℤ) + (14) * (n 63 : ℤ) + (22) * (n 67 : ℤ) + (1) * (n 71 : ℤ) + (5) * (n 75 : ℤ) + (2) * (n 79 : ℤ) + (4)
    * (n 80 : ℤ) = 12
  e23 : (1) * (n 5 : ℤ) + (6) * (n 10 : ℤ) + (1) * (n 14 : ℤ) + (4) * (n 15 : ℤ) + (1) * (n 16 : ℤ) + (2) * (n
    17 : ℤ) + (6) * (n 25 : ℤ) + (20) * (n 29 : ℤ) + (4) * (n 33 : ℤ) + (9) * (n 34 : ℤ) + (1) * (n 35 : ℤ) +
    (2) * (n 36 : ℤ) + (12) * (n 40 : ℤ) + (20) * (n 44 : ℤ) + (6) * (n 52 : ℤ) + (1) * (n 57 : ℤ) + (4) * (n 58
    : ℤ) + (2) * (n 59 : ℤ) + (12) * (n 63 : ℤ) + (30) * (n 67 : ℤ) + (6) * (n 75 : ℤ) + (1) * (n 79 : ℤ) + (4)
    * (n 80 : ℤ) + (2) * (n 81 : ℤ) = 12

set_option maxHeartbeats 1000000 in
private theorem equations {n : Fin 85 → ℕ} (h : MultiplicityConditions n) : Equations n := by
  constructor
  · have hh := h.gram_eq 0 0
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (-3) * (-3) + ((n 0 : ℤ) * (-3) * (-3) + ((n 0 : ℤ) * (-3) * (-3) + ((n 0 : ℤ) * (-3) *
      (-3) + ((n 4 : ℤ) * (-3) * (-3) + ((n 5 : ℤ) * (-3) * (-3) + ((n 6 : ℤ) * (-2) * (-2) + ((n 6 : ℤ) * (-2)
      * (-2) + ((n 6 : ℤ) * (-2) * (-2) + ((n 6 : ℤ) * (-2) * (-2) + ((n 10 : ℤ) * (-2) * (-2) + ((n 10 : ℤ) *
      (-2) * (-2) + ((n 10 : ℤ) * (-2) * (-2) + ((n 10 : ℤ) * (-2) * (-2) + ((n 14 : ℤ) * (-2) * (-2) + ((n 15 :
      ℤ) * (-2) * (-2) + ((n 16 : ℤ) * (-1) * (-1) + ((n 17 : ℤ) * (-1) * (-1) + ((n 17 : ℤ) * (-1) * (-1) + ((n
      17 : ℤ) * (-1) * (-1) + ((n 17 : ℤ) * (-1) * (-1) + ((n 21 : ℤ) * (-1) * (-1) + ((n 21 : ℤ) * (-1) * (-1)
      + ((n 21 : ℤ) * (-1) * (-1) + ((n 21 : ℤ) * (-1) * (-1) + ((n 25 : ℤ) * (-1) * (-1) + ((n 25 : ℤ) * (-1) *
      (-1) + ((n 25 : ℤ) * (-1) * (-1) + ((n 25 : ℤ) * (-1) * (-1) + ((n 29 : ℤ) * (-1) * (-1) + ((n 29 : ℤ) *
      (-1) * (-1) + ((n 29 : ℤ) * (-1) * (-1) + ((n 29 : ℤ) * (-1) * (-1) + ((n 33 : ℤ) * (-1) * (-1) + ((n 34 :
      ℤ) * (-1) * (-1) + ((n 35 : ℤ) * (0) * (0) + ((n 36 : ℤ) * (0) * (0) + ((n 36 : ℤ) * (0) * (0) + ((n 36 :
      ℤ) * (0) * (0) + ((n 36 : ℤ) * (0) * (0) + ((n 40 : ℤ) * (0) * (0) + ((n 40 : ℤ) * (0) * (0) + ((n 40 : ℤ)
      * (0) * (0) + ((n 40 : ℤ) * (0) * (0) + ((n 44 : ℤ) * (0) * (0) + ((n 44 : ℤ) * (0) * (0) + ((n 44 : ℤ) *
      (0) * (0) + ((n 44 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (1) * (1) + ((n 48 : ℤ) * (1) * (1) + ((n 48 : ℤ) *
      (1) * (1) + ((n 48 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) *
      (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 56 : ℤ) * (1) * (1) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) *
      (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) *
      (1) * (1) + ((n 63 : ℤ) * (1) * (1) + ((n 63 : ℤ) * (1) * (1) + ((n 63 : ℤ) * (1) * (1) + ((n 63 : ℤ) *
      (1) * (1) + ((n 67 : ℤ) * (1) * (1) + ((n 67 : ℤ) * (1) * (1) + ((n 67 : ℤ) * (1) * (1) + ((n 67 : ℤ) *
      (1) * (1) + ((n 71 : ℤ) * (2) * (2) + ((n 71 : ℤ) * (2) * (2) + ((n 71 : ℤ) * (2) * (2) + ((n 71 : ℤ) *
      (2) * (2) + ((n 75 : ℤ) * (2) * (2) + ((n 75 : ℤ) * (2) * (2) + ((n 75 : ℤ) * (2) * (2) + ((n 75 : ℤ) *
      (2) * (2) + ((n 79 : ℤ) * (2) * (2) + ((n 80 : ℤ) * (2) * (2) + ((n 81 : ℤ) * (3) * (3) + ((n 81 : ℤ) *
      (3) * (3) + ((n 81 : ℤ) * (3) * (3) + ((n 81 : ℤ) * (3) * (3) +
      (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 16 at hh
    linear_combination hh
  · have hh := h.gram_eq 1 1
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) +
      ((n 4 : ℤ) * (1) * (1) + ((n 5 : ℤ) * (1) * (1) + ((n 6 : ℤ) * (1) * (1) + ((n 6 : ℤ) * (1) * (1) + ((n 6
      : ℤ) * (1) * (1) + ((n 6 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 :
      ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 14 : ℤ) * (2) * (2) + ((n 15 : ℤ) * (2) * (2) + ((n 16 : ℤ)
      * (-1) * (-1) + ((n 17 : ℤ) * (0) * (0) + ((n 17 : ℤ) * (0) * (0) + ((n 17 : ℤ) * (0) * (0) + ((n 17 : ℤ)
      * (0) * (0) + ((n 21 : ℤ) * (2) * (2) + ((n 21 : ℤ) * (2) * (2) + ((n 21 : ℤ) * (2) * (2) + ((n 21 : ℤ) *
      (2) * (2) + ((n 25 : ℤ) * (2) * (2) + ((n 25 : ℤ) * (2) * (2) + ((n 25 : ℤ) * (2) * (2) + ((n 25 : ℤ) *
      (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) *
      (2) * (2) + ((n 33 : ℤ) * (3) * (3) + ((n 34 : ℤ) * (3) * (3) + ((n 35 : ℤ) * (0) * (0) + ((n 36 : ℤ) *
      (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 40 : ℤ) *
      (1) * (1) + ((n 40 : ℤ) * (1) * (1) + ((n 40 : ℤ) * (1) * (1) + ((n 40 : ℤ) * (1) * (1) + ((n 44 : ℤ) *
      (3) * (3) + ((n 44 : ℤ) * (3) * (3) + ((n 44 : ℤ) * (3) * (3) + ((n 44 : ℤ) * (3) * (3) + ((n 48 : ℤ) *
      (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 52 : ℤ) *
      (0) * (0) + ((n 52 : ℤ) * (0) * (0) + ((n 52 : ℤ) * (0) * (0) + ((n 52 : ℤ) * (0) * (0) + ((n 56 : ℤ) *
      (1) * (1) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (2) * (2) + ((n 59 : ℤ) *
      (2) * (2) + ((n 59 : ℤ) * (2) * (2) + ((n 59 : ℤ) * (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 63 : ℤ) *
      (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 67 : ℤ) * (2) * (2) + ((n 67 : ℤ) *
      (2) * (2) + ((n 67 : ℤ) * (2) * (2) + ((n 67 : ℤ) * (2) * (2) + ((n 71 : ℤ) * (1) * (1) + ((n 71 : ℤ) *
      (1) * (1) + ((n 71 : ℤ) * (1) * (1) + ((n 71 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) *
      (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 79 : ℤ) * (2) * (2) + ((n 80 : ℤ) *
      (2) * (2) + ((n 81 : ℤ) * (0) * (0) + ((n 81 : ℤ) * (0) * (0) + ((n 81 : ℤ) * (0) * (0) + ((n 81 : ℤ) *
      (0) * (0) + (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 16
      at hh
    linear_combination hh
  · have hh := h.gram_eq 2 2
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (1) * (1) +
      ((n 4 : ℤ) * (0) * (0) + ((n 5 : ℤ) * (1) * (1) + ((n 6 : ℤ) * (0) * (0) + ((n 6 : ℤ) * (0) * (0) + ((n 6
      : ℤ) * (0) * (0) + ((n 6 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 :
      ℤ) * (1) * (1) + ((n 10 : ℤ) * (2) * (2) + ((n 14 : ℤ) * (1) * (1) + ((n 15 : ℤ) * (2) * (2) + ((n 16 : ℤ)
      * (1) * (1) + ((n 17 : ℤ) * (0) * (0) + ((n 17 : ℤ) * (1) * (1) + ((n 17 : ℤ) * (1) * (1) + ((n 17 : ℤ) *
      (1) * (1) + ((n 21 : ℤ) * (0) * (0) + ((n 21 : ℤ) * (0) * (0) + ((n 21 : ℤ) * (0) * (0) + ((n 21 : ℤ) *
      (1) * (1) + ((n 25 : ℤ) * (1) * (1) + ((n 25 : ℤ) * (1) * (1) + ((n 25 : ℤ) * (1) * (1) + ((n 25 : ℤ) *
      (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) *
      (3) * (3) + ((n 33 : ℤ) * (2) * (2) + ((n 34 : ℤ) * (3) * (3) + ((n 35 : ℤ) * (1) * (1) + ((n 36 : ℤ) *
      (0) * (0) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 40 : ℤ) *
      (1) * (1) + ((n 40 : ℤ) * (2) * (2) + ((n 40 : ℤ) * (2) * (2) + ((n 40 : ℤ) * (2) * (2) + ((n 44 : ℤ) *
      (2) * (2) + ((n 44 : ℤ) * (2) * (2) + ((n 44 : ℤ) * (2) * (2) + ((n 44 : ℤ) * (3) * (3) + ((n 48 : ℤ) *
      (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (1) * (1) + ((n 52 : ℤ) *
      (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (2) * (2) + ((n 56 : ℤ) *
      (0) * (0) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (2) * (2) + ((n 59 : ℤ) * (0) * (0) + ((n 59 : ℤ) *
      (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 63 : ℤ) * (1) * (1) + ((n 63 : ℤ) *
      (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 67 : ℤ) * (2) * (2) + ((n 67 : ℤ) *
      (3) * (3) + ((n 67 : ℤ) * (3) * (3) + ((n 67 : ℤ) * (3) * (3) + ((n 71 : ℤ) * (0) * (0) + ((n 71 : ℤ) *
      (0) * (0) + ((n 71 : ℤ) * (0) * (0) + ((n 71 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) *
      (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (2) * (2) + ((n 79 : ℤ) * (1) * (1) + ((n 80 : ℤ) *
      (2) * (2) + ((n 81 : ℤ) * (0) * (0) + ((n 81 : ℤ) * (1) * (1) + ((n 81 : ℤ) * (1) * (1) + ((n 81 : ℤ) *
      (1) * (1) + (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 16
      at hh
    linear_combination hh
  · have hh := h.gram_eq 0 1
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (0)
      + ((n 4 : ℤ) * (-3) * (1) + ((n 5 : ℤ) * (-3) * (1) + ((n 6 : ℤ) * (-2) * (1) + ((n 6 : ℤ) * (-2) * (1) +
      ((n 6 : ℤ) * (-2) * (1) + ((n 6 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (1) +
      ((n 10 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (1) + ((n 14 : ℤ) * (-2) * (2) + ((n 15 : ℤ) * (-2) * (2)
      + ((n 16 : ℤ) * (-1) * (-1) + ((n 17 : ℤ) * (-1) * (0) + ((n 17 : ℤ) * (-1) * (0) + ((n 17 : ℤ) * (-1) *
      (0) + ((n 17 : ℤ) * (-1) * (0) + ((n 21 : ℤ) * (-1) * (2) + ((n 21 : ℤ) * (-1) * (2) + ((n 21 : ℤ) * (-1)
      * (2) + ((n 21 : ℤ) * (-1) * (2) + ((n 25 : ℤ) * (-1) * (2) + ((n 25 : ℤ) * (-1) * (2) + ((n 25 : ℤ) *
      (-1) * (2) + ((n 25 : ℤ) * (-1) * (2) + ((n 29 : ℤ) * (-1) * (2) + ((n 29 : ℤ) * (-1) * (2) + ((n 29 : ℤ)
      * (-1) * (2) + ((n 29 : ℤ) * (-1) * (2) + ((n 33 : ℤ) * (-1) * (3) + ((n 34 : ℤ) * (-1) * (3) + ((n 35 :
      ℤ) * (0) * (0) + ((n 36 : ℤ) * (0) * (1) + ((n 36 : ℤ) * (0) * (1) + ((n 36 : ℤ) * (0) * (1) + ((n 36 : ℤ)
      * (0) * (1) + ((n 40 : ℤ) * (0) * (1) + ((n 40 : ℤ) * (0) * (1) + ((n 40 : ℤ) * (0) * (1) + ((n 40 : ℤ) *
      (0) * (1) + ((n 44 : ℤ) * (0) * (3) + ((n 44 : ℤ) * (0) * (3) + ((n 44 : ℤ) * (0) * (3) + ((n 44 : ℤ) *
      (0) * (3) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) *
      (1) * (0) + ((n 52 : ℤ) * (1) * (0) + ((n 52 : ℤ) * (1) * (0) + ((n 52 : ℤ) * (1) * (0) + ((n 52 : ℤ) *
      (1) * (0) + ((n 56 : ℤ) * (1) * (1) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (1) * (1) + ((n 59 : ℤ) *
      (1) * (2) + ((n 59 : ℤ) * (1) * (2) + ((n 59 : ℤ) * (1) * (2) + ((n 59 : ℤ) * (1) * (2) + ((n 63 : ℤ) *
      (1) * (2) + ((n 63 : ℤ) * (1) * (2) + ((n 63 : ℤ) * (1) * (2) + ((n 63 : ℤ) * (1) * (2) + ((n 67 : ℤ) *
      (1) * (2) + ((n 67 : ℤ) * (1) * (2) + ((n 67 : ℤ) * (1) * (2) + ((n 67 : ℤ) * (1) * (2) + ((n 71 : ℤ) *
      (2) * (1) + ((n 71 : ℤ) * (2) * (1) + ((n 71 : ℤ) * (2) * (1) + ((n 71 : ℤ) * (2) * (1) + ((n 75 : ℤ) *
      (2) * (1) + ((n 75 : ℤ) * (2) * (1) + ((n 75 : ℤ) * (2) * (1) + ((n 75 : ℤ) * (2) * (1) + ((n 79 : ℤ) *
      (2) * (2) + ((n 80 : ℤ) * (2) * (2) + ((n 81 : ℤ) * (3) * (0) + ((n 81 : ℤ) * (3) * (0) + ((n 81 : ℤ) *
      (3) * (0) + ((n 81 : ℤ) * (3) * (0) +
      (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 0 at hh
    linear_combination hh
  · have hh := h.gram_eq 0 2
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (0) + ((n 0 : ℤ) * (-3) * (1)
      + ((n 4 : ℤ) * (-3) * (0) + ((n 5 : ℤ) * (-3) * (1) + ((n 6 : ℤ) * (-2) * (0) + ((n 6 : ℤ) * (-2) * (0) +
      ((n 6 : ℤ) * (-2) * (0) + ((n 6 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (1) +
      ((n 10 : ℤ) * (-2) * (1) + ((n 10 : ℤ) * (-2) * (2) + ((n 14 : ℤ) * (-2) * (1) + ((n 15 : ℤ) * (-2) * (2)
      + ((n 16 : ℤ) * (-1) * (1) + ((n 17 : ℤ) * (-1) * (0) + ((n 17 : ℤ) * (-1) * (1) + ((n 17 : ℤ) * (-1) *
      (1) + ((n 17 : ℤ) * (-1) * (1) + ((n 21 : ℤ) * (-1) * (0) + ((n 21 : ℤ) * (-1) * (0) + ((n 21 : ℤ) * (-1)
      * (0) + ((n 21 : ℤ) * (-1) * (1) + ((n 25 : ℤ) * (-1) * (1) + ((n 25 : ℤ) * (-1) * (1) + ((n 25 : ℤ) *
      (-1) * (1) + ((n 25 : ℤ) * (-1) * (2) + ((n 29 : ℤ) * (-1) * (2) + ((n 29 : ℤ) * (-1) * (2) + ((n 29 : ℤ)
      * (-1) * (2) + ((n 29 : ℤ) * (-1) * (3) + ((n 33 : ℤ) * (-1) * (2) + ((n 34 : ℤ) * (-1) * (3) + ((n 35 :
      ℤ) * (0) * (1) + ((n 36 : ℤ) * (0) * (0) + ((n 36 : ℤ) * (0) * (1) + ((n 36 : ℤ) * (0) * (1) + ((n 36 : ℤ)
      * (0) * (1) + ((n 40 : ℤ) * (0) * (1) + ((n 40 : ℤ) * (0) * (2) + ((n 40 : ℤ) * (0) * (2) + ((n 40 : ℤ) *
      (0) * (2) + ((n 44 : ℤ) * (0) * (2) + ((n 44 : ℤ) * (0) * (2) + ((n 44 : ℤ) * (0) * (2) + ((n 44 : ℤ) *
      (0) * (3) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) * (1) * (0) + ((n 48 : ℤ) *
      (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) *
      (1) * (2) + ((n 56 : ℤ) * (1) * (0) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (1) * (2) + ((n 59 : ℤ) *
      (1) * (0) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 63 : ℤ) *
      (1) * (1) + ((n 63 : ℤ) * (1) * (2) + ((n 63 : ℤ) * (1) * (2) + ((n 63 : ℤ) * (1) * (2) + ((n 67 : ℤ) *
      (1) * (2) + ((n 67 : ℤ) * (1) * (3) + ((n 67 : ℤ) * (1) * (3) + ((n 67 : ℤ) * (1) * (3) + ((n 71 : ℤ) *
      (2) * (0) + ((n 71 : ℤ) * (2) * (0) + ((n 71 : ℤ) * (2) * (0) + ((n 71 : ℤ) * (2) * (1) + ((n 75 : ℤ) *
      (2) * (1) + ((n 75 : ℤ) * (2) * (1) + ((n 75 : ℤ) * (2) * (1) + ((n 75 : ℤ) * (2) * (2) + ((n 79 : ℤ) *
      (2) * (1) + ((n 80 : ℤ) * (2) * (2) + ((n 81 : ℤ) * (3) * (0) + ((n 81 : ℤ) * (3) * (1) + ((n 81 : ℤ) *
      (3) * (1) + ((n 81 : ℤ) * (3) * (1) +
      (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 0 at hh
    linear_combination hh
  · have hh := h.gram_eq 1 2
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (1) +
      ((n 4 : ℤ) * (1) * (0) + ((n 5 : ℤ) * (1) * (1) + ((n 6 : ℤ) * (1) * (0) + ((n 6 : ℤ) * (1) * (0) + ((n 6
      : ℤ) * (1) * (0) + ((n 6 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 :
      ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (2) + ((n 14 : ℤ) * (2) * (1) + ((n 15 : ℤ) * (2) * (2) + ((n 16 : ℤ)
      * (-1) * (1) + ((n 17 : ℤ) * (0) * (0) + ((n 17 : ℤ) * (0) * (1) + ((n 17 : ℤ) * (0) * (1) + ((n 17 : ℤ) *
      (0) * (1) + ((n 21 : ℤ) * (2) * (0) + ((n 21 : ℤ) * (2) * (0) + ((n 21 : ℤ) * (2) * (0) + ((n 21 : ℤ) *
      (2) * (1) + ((n 25 : ℤ) * (2) * (1) + ((n 25 : ℤ) * (2) * (1) + ((n 25 : ℤ) * (2) * (1) + ((n 25 : ℤ) *
      (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) *
      (2) * (3) + ((n 33 : ℤ) * (3) * (2) + ((n 34 : ℤ) * (3) * (3) + ((n 35 : ℤ) * (0) * (1) + ((n 36 : ℤ) *
      (1) * (0) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 40 : ℤ) *
      (1) * (1) + ((n 40 : ℤ) * (1) * (2) + ((n 40 : ℤ) * (1) * (2) + ((n 40 : ℤ) * (1) * (2) + ((n 44 : ℤ) *
      (3) * (2) + ((n 44 : ℤ) * (3) * (2) + ((n 44 : ℤ) * (3) * (2) + ((n 44 : ℤ) * (3) * (3) + ((n 48 : ℤ) *
      (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (1) + ((n 52 : ℤ) *
      (0) * (1) + ((n 52 : ℤ) * (0) * (1) + ((n 52 : ℤ) * (0) * (1) + ((n 52 : ℤ) * (0) * (2) + ((n 56 : ℤ) *
      (1) * (0) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (1) * (2) + ((n 59 : ℤ) * (2) * (0) + ((n 59 : ℤ) *
      (2) * (1) + ((n 59 : ℤ) * (2) * (1) + ((n 59 : ℤ) * (2) * (1) + ((n 63 : ℤ) * (2) * (1) + ((n 63 : ℤ) *
      (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 67 : ℤ) * (2) * (2) + ((n 67 : ℤ) *
      (2) * (3) + ((n 67 : ℤ) * (2) * (3) + ((n 67 : ℤ) * (2) * (3) + ((n 71 : ℤ) * (1) * (0) + ((n 71 : ℤ) *
      (1) * (0) + ((n 71 : ℤ) * (1) * (0) + ((n 71 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) *
      (1) * (1) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) * (1) * (2) + ((n 79 : ℤ) * (2) * (1) + ((n 80 : ℤ) *
      (2) * (2) + ((n 81 : ℤ) * (0) * (0) + ((n 81 : ℤ) * (0) * (1) + ((n 81 : ℤ) * (0) * (1) + ((n 81 : ℤ) *
      (0) * (1) + (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 12
      at hh
    linear_combination hh
  · have hh := h.gram_eq 2 3
    conv_lhs at hh => rw [normalize h]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
    change (n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (0) + ((n 0 : ℤ) * (0) * (1) + ((n 0 : ℤ) * (1) * (0) +
      ((n 4 : ℤ) * (0) * (0) + ((n 5 : ℤ) * (1) * (1) + ((n 6 : ℤ) * (0) * (0) + ((n 6 : ℤ) * (0) * (0) + ((n 6
      : ℤ) * (0) * (1) + ((n 6 : ℤ) * (1) * (0) + ((n 10 : ℤ) * (1) * (1) + ((n 10 : ℤ) * (1) * (1) + ((n 10 :
      ℤ) * (1) * (2) + ((n 10 : ℤ) * (2) * (1) + ((n 14 : ℤ) * (1) * (1) + ((n 15 : ℤ) * (2) * (2) + ((n 16 : ℤ)
      * (1) * (1) + ((n 17 : ℤ) * (0) * (1) + ((n 17 : ℤ) * (1) * (0) + ((n 17 : ℤ) * (1) * (1) + ((n 17 : ℤ) *
      (1) * (1) + ((n 21 : ℤ) * (0) * (0) + ((n 21 : ℤ) * (0) * (0) + ((n 21 : ℤ) * (0) * (1) + ((n 21 : ℤ) *
      (1) * (0) + ((n 25 : ℤ) * (1) * (1) + ((n 25 : ℤ) * (1) * (1) + ((n 25 : ℤ) * (1) * (2) + ((n 25 : ℤ) *
      (2) * (1) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (2) + ((n 29 : ℤ) * (2) * (3) + ((n 29 : ℤ) *
      (3) * (2) + ((n 33 : ℤ) * (2) * (2) + ((n 34 : ℤ) * (3) * (3) + ((n 35 : ℤ) * (1) * (1) + ((n 36 : ℤ) *
      (0) * (1) + ((n 36 : ℤ) * (1) * (0) + ((n 36 : ℤ) * (1) * (1) + ((n 36 : ℤ) * (1) * (1) + ((n 40 : ℤ) *
      (1) * (2) + ((n 40 : ℤ) * (2) * (1) + ((n 40 : ℤ) * (2) * (2) + ((n 40 : ℤ) * (2) * (2) + ((n 44 : ℤ) *
      (2) * (2) + ((n 44 : ℤ) * (2) * (2) + ((n 44 : ℤ) * (2) * (3) + ((n 44 : ℤ) * (3) * (2) + ((n 48 : ℤ) *
      (0) * (0) + ((n 48 : ℤ) * (0) * (0) + ((n 48 : ℤ) * (0) * (1) + ((n 48 : ℤ) * (1) * (0) + ((n 52 : ℤ) *
      (1) * (1) + ((n 52 : ℤ) * (1) * (1) + ((n 52 : ℤ) * (1) * (2) + ((n 52 : ℤ) * (2) * (1) + ((n 56 : ℤ) *
      (0) * (0) + ((n 57 : ℤ) * (1) * (1) + ((n 58 : ℤ) * (2) * (2) + ((n 59 : ℤ) * (0) * (1) + ((n 59 : ℤ) *
      (1) * (0) + ((n 59 : ℤ) * (1) * (1) + ((n 59 : ℤ) * (1) * (1) + ((n 63 : ℤ) * (1) * (2) + ((n 63 : ℤ) *
      (2) * (1) + ((n 63 : ℤ) * (2) * (2) + ((n 63 : ℤ) * (2) * (2) + ((n 67 : ℤ) * (2) * (3) + ((n 67 : ℤ) *
      (3) * (2) + ((n 67 : ℤ) * (3) * (3) + ((n 67 : ℤ) * (3) * (3) + ((n 71 : ℤ) * (0) * (0) + ((n 71 : ℤ) *
      (0) * (0) + ((n 71 : ℤ) * (0) * (1) + ((n 71 : ℤ) * (1) * (0) + ((n 75 : ℤ) * (1) * (1) + ((n 75 : ℤ) *
      (1) * (1) + ((n 75 : ℤ) * (1) * (2) + ((n 75 : ℤ) * (2) * (1) + ((n 79 : ℤ) * (1) * (1) + ((n 80 : ℤ) *
      (2) * (2) + ((n 81 : ℤ) * (0) * (1) + ((n 81 : ℤ) * (1) * (0) + ((n 81 : ℤ) * (1) * (1) + ((n 81 : ℤ) *
      (1) * (1) + (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = 12
      at hh
    linear_combination hh

/-- Positivity leaves only the nine orbits occurring in M through R. -/
private theorem support {n : Fin 85 → ℕ} (h : MultiplicityConditions n) :
    n 0 = 0 ∧ n 4 = 0 ∧ n 6 = 0 ∧ n 10 = 0 ∧ n 14 = 0 ∧ n 16 = 0 ∧ n 17 = 0 ∧ n 21 = 0 ∧ n 25 = 0 ∧ n 29 = 0 ∧ n
      33 = 0 ∧ n 40 = 0 ∧ n 44 = 0 ∧ n 52 = 0 ∧ n 59 = 0 ∧ n 63 = 0 ∧ n 67 = 0 ∧ n 71 = 0 ∧ n 75 = 0 ∧ n 79 = 0
      ∧ n 80 = 0 ∧ n 81 = 0 := by
  have hp : 0 < n 56 := h.principal_pos
  have h00 := (equations h).e00
  have h11 := (equations h).e11
  have h22 := (equations h).e22
  have h01 := (equations h).e01
  have h02 := (equations h).e02
  have h12 := (equations h).e12
  have h23 := (equations h).e23
  have hc : (32) * (n 0 : ℤ) + (16) * (n 4 : ℤ) + (16) * (n 5 : ℤ) + (32) * (n 6 : ℤ) + (32) * (n 10 : ℤ) + (16)
    * (n 14 : ℤ) + (16) * (n 15 : ℤ) + (32) * (n 21 : ℤ) + (32) * (n 25 : ℤ) + (32) * (n 29 : ℤ) + (16) * (n 33
    : ℤ) + (16) * (n 34 : ℤ) + (32) * (n 44 : ℤ) + (32) * (n 81 : ℤ) = 16 := by
    linear_combination (1 : ℤ) * h00 + (1 : ℤ) * h11 + (-4 : ℤ) * h22 + (-2 : ℤ) * h01 + (4 : ℤ) * h23
  have hz : n 0 = 0 ∧ n 6 = 0 ∧ n 10 = 0 ∧ n 21 = 0 ∧ n 25 = 0 ∧ n 29 = 0 ∧ n 44 = 0 ∧ n 81 = 0 := by
    clear * - hc hp
    omega
  obtain ⟨z0, z6, z10, z21, z25, z29, z44, z81⟩ := hz
  simp only [z0, z6, z10, z21, z25, z29, z44, z81, Nat.cast_zero, mul_zero, zero_add, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (9) * (n 4 : ℤ) + (9) * (n 5 : ℤ) + (4) * (n 14 : ℤ) + (4) * (n 15 : ℤ) + (1) * (n 16 : ℤ) + (4) *
    (n 17 : ℤ) + (1) * (n 33 : ℤ) + (1) * (n 34 : ℤ) + (4) * (n 48 : ℤ) + (4) * (n 52 : ℤ) + (1) * (n 56 : ℤ) +
    (1) * (n 57 : ℤ) + (1) * (n 58 : ℤ) + (4) * (n 59 : ℤ) + (4) * (n 63 : ℤ) + (4) * (n 67 : ℤ) + (16) * (n 71
    : ℤ) + (16) * (n 75 : ℤ) + (4) * (n 79 : ℤ) + (4) * (n 80 : ℤ) = 16 := by
    linear_combination (1 : ℤ) * h00
  have hz : n 71 = 0 ∧ n 75 = 0 := by
    clear * - hc hp
    omega
  obtain ⟨z71, z75⟩ := hz
  simp only [z71, z75, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (1) * (n 4 : ℤ) + (1) * (n 5 : ℤ) + (4) * (n 14 : ℤ) + (4) * (n 15 : ℤ) + (1) * (n 16 : ℤ) + (9) *
    (n 33 : ℤ) + (9) * (n 34 : ℤ) + (4) * (n 36 : ℤ) + (4) * (n 40 : ℤ) + (1) * (n 56 : ℤ) + (1) * (n 57 : ℤ) +
    (1) * (n 58 : ℤ) + (16) * (n 59 : ℤ) + (16) * (n 63 : ℤ) + (16) * (n 67 : ℤ) + (4) * (n 79 : ℤ) + (4) * (n
    80 : ℤ) = 16 := by
    linear_combination (1 : ℤ) * h11
  have hz : n 59 = 0 ∧ n 63 = 0 ∧ n 67 = 0 := by
    clear * - hc hp
    omega
  obtain ⟨z59, z63, z67⟩ := hz
  simp only [z59, z63, z67, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (16) * (n 16 : ℤ) + (12) * (n 17 : ℤ) + (4) * (n 35 : ℤ) + (12) * (n 40 : ℤ) + (20) * (n 52 : ℤ) +
    (4) * (n 56 : ℤ) + (4) * (n 58 : ℤ) + (4) * (n 79 : ℤ) = 16 := by
    linear_combination (3 : ℤ) * h11 + (1 : ℤ) * h22 + (1 : ℤ) * h01 + (-1 : ℤ) * h02 + (-7 : ℤ) * h12 + (3 : ℤ)
      * h23
  have hz : n 16 = 0 ∧ n 52 = 0 := by
    clear * - hc hp
    omega
  obtain ⟨z16, z52⟩ := hz
  simp only [z16, z52, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (64) * (n 5 : ℤ) + (48) * (n 15 : ℤ) + (128) * (n 17 : ℤ) + (32) * (n 34 : ℤ) + (16) * (n 35 : ℤ) +
    (64) * (n 40 : ℤ) + (32) * (n 56 : ℤ) + (48) * (n 79 : ℤ) = 144 := by
    linear_combination (5 : ℤ) * h00 + (9 : ℤ) * h11 + (4 : ℤ) * h22 + (18 : ℤ) * h01 + (-24 : ℤ) * h02 + (-24 :
      ℤ) * h12 + (12 : ℤ) * h23
  have hz : n 17 = 0 := by
    clear * - hc hp
    omega
  have z17 := hz
  simp only [z17, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (16) * (n 4 : ℤ) + (16) * (n 15 : ℤ) + (16) * (n 33 : ℤ) + (64) * (n 34 : ℤ) + (16) * (n 35 : ℤ) +
    (128) * (n 40 : ℤ) + (16) * (n 57 : ℤ) + (64) * (n 58 : ℤ) + (16) * (n 79 : ℤ) + (64) * (n 80 : ℤ) = 80 :=
    by
    linear_combination (1 : ℤ) * h00 + (1 : ℤ) * h11 + (-12 : ℤ) * h22 + (-2 : ℤ) * h01 + (8 : ℤ) * h02 + (-8 :
      ℤ) * h12 + (28 : ℤ) * h23
  have hz : n 40 = 0 := by
    clear * - hc hp
    omega
  have z40 := hz
  simp only [z40, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (24) * (n 4 : ℤ) + (16) * (n 14 : ℤ) + (24) * (n 33 : ℤ) + (16) * (n 34 : ℤ) + (8) * (n 57 : ℤ) +
    (16) * (n 58 : ℤ) + (16) * (n 79 : ℤ) + (32) * (n 80 : ℤ) = 16 := by
    linear_combination (1 : ℤ) * h00 + (3 : ℤ) * h11 + (-12 : ℤ) * h22 + (-4 : ℤ) * h01 + (8 : ℤ) * h02 + (12 :
      ℤ) * h23
  have hz : n 4 = 0 ∧ n 33 = 0 ∧ n 80 = 0 := by
    clear * - hc hp
    omega
  obtain ⟨z4, z33, z80⟩ := hz
  simp only [z4, z33, z80, Nat.cast_zero, mul_zero, zero_add, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (16) * (n 5 : ℤ) + (16) * (n 56 : ℤ) + (8) * (n 57 : ℤ) + (48) * (n 79 : ℤ) = 48 := by
    linear_combination (3 : ℤ) * h00 + (5 : ℤ) * h11 + (-8 : ℤ) * h22 + (8 : ℤ) * h01 + (-4 : ℤ) * h02 + (-4 :
      ℤ) * h12 + (8 : ℤ) * h23
  have hz : n 79 = 0 := by
    clear * - hc hp
    omega
  have z79 := hz
  simp only [z79, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hc : (4) * (n 14 : ℤ) = 0 := by
    linear_combination (1 : ℤ) * h11 + (-1 : ℤ) * h22 + (-1 : ℤ) * h01 + (1 : ℤ) * h02 + (-1 : ℤ) * h12 + (1 :
      ℤ) * h23
  have hz : n 14 = 0 := by
    clear * - hc hp
    omega
  have z14 := hz
  simp only [z14, Nat.cast_zero, mul_zero, add_zero] at h00 h11 h22 h01 h02 h12 h23
  exact ⟨z0, z4, z6, z10, z14, z16, z17, z21, z25, z29, z33, z40, z44, z52, z59, z63, z67, z71, z75, z79, z80, z81⟩

/-- Full catalogue multiplicities for M, N, P, Q, and R, respectively. -/
private def counts : Fin 5 → Fin 85 → ℕ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
    2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
    3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 500000 in
private theorem classified_vectors {n : Fin 85 → ℕ} (h : MultiplicityConditions n) :
    n = counts 0 ∨ n = counts 1 ∨ n = counts 2 ∨ n = counts 3 ∨ n = counts 4 := by
  have hp : 0 < n 56 := h.principal_pos
  obtain ⟨z0, z4, z6, z10, z14, z16, z17, z21, z25, z29, z33, z40, z44, z52, z59, z63, z67, z71, z75, z79, z80,
    z81⟩ := support h
  obtain ⟨h00, h11, h22, h01, h02, h12, h23⟩ := equations h
  simp only [z0, z4, z6, z10, z14, z16, z17, z21, z25, z29, z33, z40, z44, z52, z59, z63, z67, z71, z75, z79, z80, z81, Nat.cast_zero, mul_zero, zero_add, add_zero] at h00 h11 h22 h01 h02 h12 h23
  have hsum : n 5 + n 15 + n 34 = 1 := by
    have hh : 16 * ((1) * (n 5 : ℤ) + (1) * (n 15 : ℤ) + (1) * (n 34 : ℤ)) = 16 := by
      linear_combination (1 : ℤ) * h00 + (-3 : ℤ) * h11 + (2 : ℤ) * h01 + (-4 : ℤ) * h02 + (4 : ℤ) * h12
    clear * - hh
    omega
  have p36 : n 36 = 3 * n 5 + 2 * n 15 + n 34 := by
    have hh : 4 * ((-3) * (n 5 : ℤ) + (-2) * (n 15 : ℤ) + (-1) * (n 34 : ℤ) + (1) * (n 36 : ℤ)) = 0 := by
      linear_combination (-1 : ℤ) * h00 + (4 : ℤ) * h11 + (-3 : ℤ) * h01 + (4 : ℤ) * h02 + (-4 : ℤ) * h12
    clear * - hh
    omega
  have p48 : n 48 = n 5 + 2 * n 15 + 3 * n 34 := by
    have hh : 4 * ((-1) * (n 5 : ℤ) + (-2) * (n 15 : ℤ) + (-3) * (n 34 : ℤ) + (1) * (n 48 : ℤ)) = 0 := by
      linear_combination (3 : ℤ) * h11 + (-3 : ℤ) * h01 + (4 : ℤ) * h02 + (-4 : ℤ) * h12
    clear * - hh
    omega
  have p56 : n 56 = n 5 + 2 * n 15 + 3 * n 34 + n 58 := by
    have hh : 4 * ((-1) * (n 5 : ℤ) + (-2) * (n 15 : ℤ) + (-3) * (n 34 : ℤ) + (1) * (n 56 : ℤ) + (-1) * (n 58 :
      ℤ)) = 0 := by
      linear_combination (3 : ℤ) * h11 + (1 : ℤ) * h01 + (-4 : ℤ) * h12
    clear * - hh
    omega
  have p57 : n 57 + 2 * n 58 = 2 * n 5 + 2 * n 15 := by
    have hh : 4 * ((-2) * (n 5 : ℤ) + (-2) * (n 15 : ℤ) + (1) * (n 57 : ℤ) + (2) * (n 58 : ℤ)) = 0 := by
      linear_combination (-3 : ℤ) * h11 + (3 : ℤ) * h01 + (4 : ℤ) * h12
    clear * - hh
    omega
  have p35 : n 35 + 2 * n 58 = 3 * n 5 + 2 * n 15 + n 34 := by
    have hh : 4 * ((-3) * (n 5 : ℤ) + (-2) * (n 15 : ℤ) + (-1) * (n 34 : ℤ) + (1) * (n 35 : ℤ) + (2) * (n 58 :
      ℤ)) = 0 := by
      linear_combination (-1 : ℤ) * h00 + (4 : ℤ) * h22 + (1 : ℤ) * h01 + (-4 : ℤ) * h12
    clear * - hh
    omega
  clear h00 h11 h22 h01 h02 h12 h23
  have hc :
      (n 5 = 0 ∧ n 15 = 0 ∧ n 34 = 1 ∧ n 35 = 1 ∧ n 36 = 1 ∧ n 48 = 3 ∧ n 56 = 3 ∧ n 57 = 0 ∧ n 58 = 0) ∨
      (n 5 = 0 ∧ n 15 = 1 ∧ n 34 = 0 ∧ n 35 = 0 ∧ n 36 = 2 ∧ n 48 = 2 ∧ n 56 = 3 ∧ n 57 = 0 ∧ n 58 = 1) ∨
      (n 5 = 0 ∧ n 15 = 1 ∧ n 34 = 0 ∧ n 35 = 2 ∧ n 36 = 2 ∧ n 48 = 2 ∧ n 56 = 2 ∧ n 57 = 2 ∧ n 58 = 0) ∨
      (n 5 = 1 ∧ n 15 = 0 ∧ n 34 = 0 ∧ n 35 = 1 ∧ n 36 = 3 ∧ n 48 = 1 ∧ n 56 = 2 ∧ n 57 = 0 ∧ n 58 = 1) ∨
      (n 5 = 1 ∧ n 15 = 0 ∧ n 34 = 0 ∧ n 35 = 3 ∧ n 36 = 3 ∧ n 48 = 1 ∧ n 56 = 1 ∧ n 57 = 2 ∧ n 58 = 0) := by
    have hcases : n 5 = 1 ∨ n 15 = 1 ∨ n 34 = 1 := by
      clear * - hsum
      omega
    rcases hcases with h5 | h15 | h34
    · by_cases h58 : n 58 = 0
      · right; right; right; right
        omega
      · right; right; right; left
        omega
    · by_cases h58 : n 58 = 0
      · right; right; left
        omega
      · right; left
        omega
    · left
      omega
  rcases hc with hc | hc | hc | hc | hc
  · left
    obtain ⟨c5, c15, c34, c35, c36, c48, c56, c57, c58⟩ := hc
    have hr : ∀ a : Fin 31, n (representative a) = counts 0 (representative a) := by
      intro a
      fin_cases a
      · exact z0
      · exact z4
      · exact c5
      · exact z6
      · exact z10
      · exact z14
      · exact c15
      · exact z16
      · exact z17
      · exact z21
      · exact z25
      · exact z29
      · exact z33
      · exact c34
      · exact c35
      · exact c36
      · exact z40
      · exact z44
      · exact c48
      · exact z52
      · exact c56
      · exact c57
      · exact c58
      · exact z59
      · exact z63
      · exact z67
      · exact z71
      · exact z75
      · exact z79
      · exact z80
      · exact z81
    funext a
    rw [congrFun (normalize h) a, hr]
    exact congrFun (by decide +kernel : (fun a => counts 0 (representative (orbitIndex a))) = counts 0) a
  · right; left
    obtain ⟨c5, c15, c34, c35, c36, c48, c56, c57, c58⟩ := hc
    have hr : ∀ a : Fin 31, n (representative a) = counts 1 (representative a) := by
      intro a
      fin_cases a
      · exact z0
      · exact z4
      · exact c5
      · exact z6
      · exact z10
      · exact z14
      · exact c15
      · exact z16
      · exact z17
      · exact z21
      · exact z25
      · exact z29
      · exact z33
      · exact c34
      · exact c35
      · exact c36
      · exact z40
      · exact z44
      · exact c48
      · exact z52
      · exact c56
      · exact c57
      · exact c58
      · exact z59
      · exact z63
      · exact z67
      · exact z71
      · exact z75
      · exact z79
      · exact z80
      · exact z81
    funext a
    rw [congrFun (normalize h) a, hr]
    exact congrFun (by decide +kernel : (fun a => counts 1 (representative (orbitIndex a))) = counts 1) a
  · right; right; left
    obtain ⟨c5, c15, c34, c35, c36, c48, c56, c57, c58⟩ := hc
    have hr : ∀ a : Fin 31, n (representative a) = counts 2 (representative a) := by
      intro a
      fin_cases a
      · exact z0
      · exact z4
      · exact c5
      · exact z6
      · exact z10
      · exact z14
      · exact c15
      · exact z16
      · exact z17
      · exact z21
      · exact z25
      · exact z29
      · exact z33
      · exact c34
      · exact c35
      · exact c36
      · exact z40
      · exact z44
      · exact c48
      · exact z52
      · exact c56
      · exact c57
      · exact c58
      · exact z59
      · exact z63
      · exact z67
      · exact z71
      · exact z75
      · exact z79
      · exact z80
      · exact z81
    funext a
    rw [congrFun (normalize h) a, hr]
    exact congrFun (by decide +kernel : (fun a => counts 2 (representative (orbitIndex a))) = counts 2) a
  · right; right; right; left
    obtain ⟨c5, c15, c34, c35, c36, c48, c56, c57, c58⟩ := hc
    have hr : ∀ a : Fin 31, n (representative a) = counts 3 (representative a) := by
      intro a
      fin_cases a
      · exact z0
      · exact z4
      · exact c5
      · exact z6
      · exact z10
      · exact z14
      · exact c15
      · exact z16
      · exact z17
      · exact z21
      · exact z25
      · exact z29
      · exact z33
      · exact c34
      · exact c35
      · exact c36
      · exact z40
      · exact z44
      · exact c48
      · exact z52
      · exact c56
      · exact c57
      · exact c58
      · exact z59
      · exact z63
      · exact z67
      · exact z71
      · exact z75
      · exact z79
      · exact z80
      · exact z81
    funext a
    rw [congrFun (normalize h) a, hr]
    exact congrFun (by decide +kernel : (fun a => counts 3 (representative (orbitIndex a))) = counts 3) a
  · right; right; right; right
    obtain ⟨c5, c15, c34, c35, c36, c48, c56, c57, c58⟩ := hc
    have hr : ∀ a : Fin 31, n (representative a) = counts 4 (representative a) := by
      intro a
      fin_cases a
      · exact z0
      · exact z4
      · exact c5
      · exact z6
      · exact z10
      · exact z14
      · exact c15
      · exact z16
      · exact z17
      · exact z21
      · exact z25
      · exact z29
      · exact z33
      · exact c34
      · exact c35
      · exact c36
      · exact z40
      · exact z44
      · exact c48
      · exact z52
      · exact c56
      · exact c57
      · exact c58
      · exact z59
      · exact z63
      · exact z67
      · exact z71
      · exact z75
      · exact z79
      · exact z80
      · exact z81
    funext a
    rw [congrFun (normalize h) a, hr]
    exact congrFun (by decide +kernel : (fun a => counts 4 (representative (orbitIndex a))) = counts 4) a

/-- Injectivity handles catalogue rows; matrix coverage handles all other rows. -/
private theorem counts_transfer {n : Fin 85 → ℕ} {c : TableICase} {v : c.Variant}
    (hn : ∀ a, n a = Fintype.card {j // tableIMatrix c v j = row a})
    (hs : ∀ j, ∃ a, row a = tableIMatrix c v j) (r : TableIRow) :
    (∑ a, if row a = r then n a else 0) =
      Fintype.card {j // tableIMatrix c v j = r} := by
  classical
  by_cases hr : ∃ a, row a = r
  · obtain ⟨a, rfl⟩ := hr
    have he (b : Fin 85) : row b = row a ↔ b = a := row_injective.eq_iff
    simpa only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hn a
  · have he (a : Fin 85) : row a ≠ r := fun ha => hr ⟨a, ha⟩
    simp only [if_neg (he _), Finset.sum_const_zero]
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun j => ?_⟩
    obtain ⟨a, ha⟩ := hs j.1
    exact hr ⟨a, ha.trans j.2⟩

private theorem counts_M :
    (∀ a, counts 0 a = Fintype.card {j // tableIMatrix .M () j = row a}) ∧
    (∀ j, ∃ a, row a = tableIMatrix .M () j) := by
  decide +kernel

private theorem counts_N :
    (∀ a, counts 1 a = Fintype.card {j // tableIMatrix .N () j = row a}) ∧
    (∀ j, ∃ a, row a = tableIMatrix .N () j) := by
  decide +kernel

private theorem counts_P :
    (∀ a, counts 2 a = Fintype.card {j // tableIMatrix .P () j = row a}) ∧
    (∀ j, ∃ a, row a = tableIMatrix .P () j) := by
  decide +kernel

private theorem counts_Q :
    (∀ a, counts 3 a = Fintype.card {j // tableIMatrix .Q () j = row a}) ∧
    (∀ j, ∃ a, row a = tableIMatrix .Q () j) := by
  decide +kernel

private theorem counts_R :
    (∀ a, counts 4 a = Fintype.card {j // tableIMatrix .R () j = row a}) ∧
    (∀ j, ∃ a, row a = tableIMatrix .R () j) := by
  decide +kernel

/-- The full multiplicities satisfying the sparse Gram system are precisely
those of one of the five cases M, N, P, Q, R of Table I. -/
theorem multiplicities_classified (n : Fin 85 → ℕ) (h : MultiplicityConditions n) :
    ∃ (c : TableICase) (v : c.Variant), ∀ r : TableIRow,
      (∑ a, if row a = r then n a else 0) =
        Fintype.card {j // tableIMatrix c v j = r} := by
  rcases classified_vectors h with hn | hn | hn | hn | hn
  · subst n
    exact ⟨.M, (), counts_transfer counts_M.1 counts_M.2⟩
  · subst n
    exact ⟨.N, (), counts_transfer counts_N.1 counts_N.2⟩
  · subst n
    exact ⟨.P, (), counts_transfer counts_P.1 counts_P.2⟩
  · subst n
    exact ⟨.Q, (), counts_transfer counts_Q.1 counts_Q.2⟩
  · subst n
    exact ⟨.R, (), counts_transfer counts_R.1 counts_R.2⟩

end Stellmacher.Recognition.LyonsU3Four.TableISparseRows
