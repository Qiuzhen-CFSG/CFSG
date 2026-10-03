module

public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeRows
import Mathlib.Tactic.LinearCombination

/-!
# Classification of sparse opposite orbit multiplicities

The eight orbit Gram equations, principal positivity, and positivity on the
opposite-orbit sum force every multiplicity vector to be one of the four
explicit vectors corresponding to cases S, T, U, and V.

Ten shared weighted bounds eliminate forty coordinates: a nonnegative integer
coordinate vanishes when its coefficient exceeds the bound. Negative terms
in later bounds have already vanished. Seven linear identities on the eleven
remaining coordinates then give the four cases. The evaluations of the model
vectors are checked separately from this arithmetic.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 379–380,
Cases 7–8.
-/

open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows

set_option maxRecDepth 2048 in
private theorem equation0 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (36) * (m 0 : ℤ) + (9) * (m 1 : ℤ) + (9) * (m 2 : ℤ) + (16) * (m 3 : ℤ) + (8) * (m 4 : ℤ) + (16)
      * (m 5 : ℤ) + (16) * (m 6 : ℤ) + (4) * (m 7 : ℤ) + (4) * (m 8 : ℤ) + (m 9 : ℤ) + (4) * (m 10 :
      ℤ) + (4) * (m 11 : ℤ) + (2) * (m 12 : ℤ) + (4) * (m 13 : ℤ) + (2) * (m 14 : ℤ) + (4) * (m 15 :
      ℤ) + (4) * (m 16 : ℤ) + (4) * (m 17 : ℤ) + (m 18 : ℤ) + (m 19 : ℤ) + (4) * (m 30 : ℤ) + (2) *
      (m 31 : ℤ) + (4) * (m 32 : ℤ) + (4) * (m 33 : ℤ) + (m 34 : ℤ) + (m 35 : ℤ) + (m 36 : ℤ) + (4)
      * (m 37 : ℤ) + (4) * (m 38 : ℤ) + (4) * (m 39 : ℤ) + (4) * (m 40 : ℤ) + (2) * (m 41 : ℤ) +
      (16) * (m 42 : ℤ) + (8) * (m 43 : ℤ) + (16) * (m 44 : ℤ) + (16) * (m 45 : ℤ) + (4) * (m 46 :
      ℤ) + (4) * (m 47 : ℤ) + (36) * (m 48 : ℤ) + (36) * (m 49 : ℤ) + (18) * (m 50 : ℤ) = 16 := by
  have hh := h.gram 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (36) + ((m 1 : ℤ) * (9) + ((m 2 : ℤ) * (9) + ((m 3 : ℤ) * (16) + ((m 4 : ℤ) *
    (8) + ((m 5 : ℤ) * (16) + ((m 6 : ℤ) * (16) + ((m 7 : ℤ) * (4) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) *
    (1) + ((m 10 : ℤ) * (4) + ((m 11 : ℤ) * (4) + ((m 12 : ℤ) * (2) + ((m 13 : ℤ) * (4) + ((m 14 :
    ℤ) * (2) + ((m 15 : ℤ) * (4) + ((m 16 : ℤ) * (4) + ((m 17 : ℤ) * (4) + ((m 18 : ℤ) * (1) + ((m
    19 : ℤ) * (1) + ((m 20 : ℤ) * (0) + ((m 21 : ℤ) * (0) + ((m 22 : ℤ) * (0) + ((m 23 : ℤ) * (0) +
    ((m 24 : ℤ) * (0) + ((m 25 : ℤ) * (0) + ((m 26 : ℤ) * (0) + ((m 27 : ℤ) * (0) + ((m 28 : ℤ) *
    (0) + ((m 29 : ℤ) * (0) + ((m 30 : ℤ) * (4) + ((m 31 : ℤ) * (2) + ((m 32 : ℤ) * (4) + ((m 33 :
    ℤ) * (4) + ((m 34 : ℤ) * (1) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (1) + ((m 37 : ℤ) * (4) + ((m
    38 : ℤ) * (4) + ((m 39 : ℤ) * (4) + ((m 40 : ℤ) * (4) + ((m 41 : ℤ) * (2) + ((m 42 : ℤ) * (16) +
    ((m 43 : ℤ) * (8) + ((m 44 : ℤ) * (16) + ((m 45 : ℤ) * (16) + ((m 46 : ℤ) * (4) + ((m 47 : ℤ) *
    (4) + ((m 48 : ℤ) * (36) + ((m 49 : ℤ) * (36) + ((m 50 : ℤ) * (18) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 16 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation1 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (-3) * (m 1 : ℤ) + (-3) * (m 2 : ℤ) + (-8) * (m 5 : ℤ) + (-8) * (m 6 : ℤ) + (-4) * (m 7 : ℤ) +
      (-4) * (m 8 : ℤ) + (m 9 : ℤ) + (-4) * (m 11 : ℤ) + (-2) * (m 12 : ℤ) + (-4) * (m 13 : ℤ) +
      (-2) * (m 14 : ℤ) + (-8) * (m 15 : ℤ) + (-8) * (m 16 : ℤ) + (-8) * (m 17 : ℤ) + (-3) * (m 18 :
      ℤ) + (-3) * (m 19 : ℤ) + (-4) * (m 30 : ℤ) + (-2) * (m 31 : ℤ) + (m 34 : ℤ) + (m 35 : ℤ) + (m
      36 : ℤ) + (8) * (m 37 : ℤ) + (8) * (m 38 : ℤ) + (8) * (m 39 : ℤ) + (12) * (m 40 : ℤ) + (6) *
      (m 41 : ℤ) + (8) * (m 44 : ℤ) + (8) * (m 45 : ℤ) + (4) * (m 46 : ℤ) + (4) * (m 47 : ℤ) + (12)
      * (m 49 : ℤ) + (6) * (m 50 : ℤ) = 0 := by
  have hh := h.gram 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (0) + ((m 1 : ℤ) * (-3) + ((m 2 : ℤ) * (-3) + ((m 3 : ℤ) * (0) + ((m 4 : ℤ) *
    (0) + ((m 5 : ℤ) * (-8) + ((m 6 : ℤ) * (-8) + ((m 7 : ℤ) * (-4) + ((m 8 : ℤ) * (-4) + ((m 9 : ℤ)
    * (1) + ((m 10 : ℤ) * (0) + ((m 11 : ℤ) * (-4) + ((m 12 : ℤ) * (-2) + ((m 13 : ℤ) * (-4) + ((m
    14 : ℤ) * (-2) + ((m 15 : ℤ) * (-8) + ((m 16 : ℤ) * (-8) + ((m 17 : ℤ) * (-8) + ((m 18 : ℤ) *
    (-3) + ((m 19 : ℤ) * (-3) + ((m 20 : ℤ) * (0) + ((m 21 : ℤ) * (0) + ((m 22 : ℤ) * (0) + ((m 23 :
    ℤ) * (0) + ((m 24 : ℤ) * (0) + ((m 25 : ℤ) * (0) + ((m 26 : ℤ) * (0) + ((m 27 : ℤ) * (0) + ((m
    28 : ℤ) * (0) + ((m 29 : ℤ) * (0) + ((m 30 : ℤ) * (-4) + ((m 31 : ℤ) * (-2) + ((m 32 : ℤ) * (0)
    + ((m 33 : ℤ) * (0) + ((m 34 : ℤ) * (1) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (1) + ((m 37 : ℤ) *
    (8) + ((m 38 : ℤ) * (8) + ((m 39 : ℤ) * (8) + ((m 40 : ℤ) * (12) + ((m 41 : ℤ) * (6) + ((m 42 :
    ℤ) * (0) + ((m 43 : ℤ) * (0) + ((m 44 : ℤ) * (8) + ((m 45 : ℤ) * (8) + ((m 46 : ℤ) * (4) + ((m
    47 : ℤ) * (4) + ((m 48 : ℤ) * (0) + ((m 49 : ℤ) * (12) + ((m 50 : ℤ) * (6) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 0 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation2 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (-3) * (m 0 : ℤ) + (-3) * (m 2 : ℤ) + (-4) * (m 3 : ℤ) + (-2) * (m 4 : ℤ) + (-2) * (m 5 : ℤ) +
      (-10) * (m 6 : ℤ) + (-2) * (m 7 : ℤ) + (-4) * (m 8 : ℤ) + (-1) * (m 9 : ℤ) + (-3) * (m 10 : ℤ)
      + (-2) * (m 11 : ℤ) + (-1) * (m 12 : ℤ) + (-6) * (m 13 : ℤ) + (-3) * (m 14 : ℤ) + (-1) * (m 15
      : ℤ) + (-5) * (m 16 : ℤ) + (-9) * (m 17 : ℤ) + (-2) * (m 18 : ℤ) + (-3) * (m 19 : ℤ) + (2) *
      (m 30 : ℤ) + (m 31 : ℤ) + (m 32 : ℤ) + (5) * (m 33 : ℤ) + (m 35 : ℤ) + (2) * (m 36 : ℤ) + (3)
      * (m 37 : ℤ) + (7) * (m 38 : ℤ) + (11) * (m 39 : ℤ) + (10) * (m 40 : ℤ) + (5) * (m 41 : ℤ) +
      (4) * (m 42 : ℤ) + (2) * (m 43 : ℤ) + (2) * (m 44 : ℤ) + (10) * (m 45 : ℤ) + (2) * (m 46 : ℤ)
      + (4) * (m 47 : ℤ) + (9) * (m 48 : ℤ) + (6) * (m 49 : ℤ) + (3) * (m 50 : ℤ) = 0 := by
  have hh := h.gram 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (-3) + ((m 1 : ℤ) * (0) + ((m 2 : ℤ) * (-3) + ((m 3 : ℤ) * (-4) + ((m 4 : ℤ) *
    (-2) + ((m 5 : ℤ) * (-2) + ((m 6 : ℤ) * (-10) + ((m 7 : ℤ) * (-2) + ((m 8 : ℤ) * (-4) + ((m 9 :
    ℤ) * (-1) + ((m 10 : ℤ) * (-3) + ((m 11 : ℤ) * (-2) + ((m 12 : ℤ) * (-1) + ((m 13 : ℤ) * (-6) +
    ((m 14 : ℤ) * (-3) + ((m 15 : ℤ) * (-1) + ((m 16 : ℤ) * (-5) + ((m 17 : ℤ) * (-9) + ((m 18 : ℤ)
    * (-2) + ((m 19 : ℤ) * (-3) + ((m 20 : ℤ) * (0) + ((m 21 : ℤ) * (0) + ((m 22 : ℤ) * (0) + ((m 23
    : ℤ) * (0) + ((m 24 : ℤ) * (0) + ((m 25 : ℤ) * (0) + ((m 26 : ℤ) * (0) + ((m 27 : ℤ) * (0) + ((m
    28 : ℤ) * (0) + ((m 29 : ℤ) * (0) + ((m 30 : ℤ) * (2) + ((m 31 : ℤ) * (1) + ((m 32 : ℤ) * (1) +
    ((m 33 : ℤ) * (5) + ((m 34 : ℤ) * (0) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (2) + ((m 37 : ℤ) *
    (3) + ((m 38 : ℤ) * (7) + ((m 39 : ℤ) * (11) + ((m 40 : ℤ) * (10) + ((m 41 : ℤ) * (5) + ((m 42 :
    ℤ) * (4) + ((m 43 : ℤ) * (2) + ((m 44 : ℤ) * (2) + ((m 45 : ℤ) * (10) + ((m 46 : ℤ) * (2) + ((m
    47 : ℤ) * (4) + ((m 48 : ℤ) * (9) + ((m 49 : ℤ) * (6) + ((m 50 : ℤ) * (3) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 0 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation3 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (m 1 : ℤ) + (m 2 : ℤ) + (4) * (m 5 : ℤ) + (4) * (m 6 : ℤ) + (4) * (m 7 : ℤ) + (4) * (m 8 : ℤ) +
      (m 9 : ℤ) + (4) * (m 11 : ℤ) + (2) * (m 12 : ℤ) + (4) * (m 13 : ℤ) + (2) * (m 14 : ℤ) + (16) *
      (m 15 : ℤ) + (16) * (m 16 : ℤ) + (16) * (m 17 : ℤ) + (9) * (m 18 : ℤ) + (9) * (m 19 : ℤ) + (4)
      * (m 21 : ℤ) + (4) * (m 22 : ℤ) + (16) * (m 23 : ℤ) + (8) * (m 24 : ℤ) + (16) * (m 25 : ℤ) +
      (8) * (m 26 : ℤ) + (16) * (m 27 : ℤ) + (8) * (m 28 : ℤ) + (36) * (m 29 : ℤ) + (4) * (m 30 : ℤ)
      + (2) * (m 31 : ℤ) + (m 34 : ℤ) + (m 35 : ℤ) + (m 36 : ℤ) + (16) * (m 37 : ℤ) + (16) * (m 38 :
      ℤ) + (16) * (m 39 : ℤ) + (36) * (m 40 : ℤ) + (18) * (m 41 : ℤ) + (4) * (m 44 : ℤ) + (4) * (m
      45 : ℤ) + (4) * (m 46 : ℤ) + (4) * (m 47 : ℤ) + (4) * (m 49 : ℤ) + (2) * (m 50 : ℤ) = 16 := by
  have hh := h.gram 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (0) + ((m 1 : ℤ) * (1) + ((m 2 : ℤ) * (1) + ((m 3 : ℤ) * (0) + ((m 4 : ℤ) * (0)
    + ((m 5 : ℤ) * (4) + ((m 6 : ℤ) * (4) + ((m 7 : ℤ) * (4) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) * (1) +
    ((m 10 : ℤ) * (0) + ((m 11 : ℤ) * (4) + ((m 12 : ℤ) * (2) + ((m 13 : ℤ) * (4) + ((m 14 : ℤ) *
    (2) + ((m 15 : ℤ) * (16) + ((m 16 : ℤ) * (16) + ((m 17 : ℤ) * (16) + ((m 18 : ℤ) * (9) + ((m 19
    : ℤ) * (9) + ((m 20 : ℤ) * (0) + ((m 21 : ℤ) * (4) + ((m 22 : ℤ) * (4) + ((m 23 : ℤ) * (16) +
    ((m 24 : ℤ) * (8) + ((m 25 : ℤ) * (16) + ((m 26 : ℤ) * (8) + ((m 27 : ℤ) * (16) + ((m 28 : ℤ) *
    (8) + ((m 29 : ℤ) * (36) + ((m 30 : ℤ) * (4) + ((m 31 : ℤ) * (2) + ((m 32 : ℤ) * (0) + ((m 33 :
    ℤ) * (0) + ((m 34 : ℤ) * (1) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (1) + ((m 37 : ℤ) * (16) + ((m
    38 : ℤ) * (16) + ((m 39 : ℤ) * (16) + ((m 40 : ℤ) * (36) + ((m 41 : ℤ) * (18) + ((m 42 : ℤ) *
    (0) + ((m 43 : ℤ) * (0) + ((m 44 : ℤ) * (4) + ((m 45 : ℤ) * (4) + ((m 46 : ℤ) * (4) + ((m 47 :
    ℤ) * (4) + ((m 48 : ℤ) * (0) + ((m 49 : ℤ) * (4) + ((m 50 : ℤ) * (2) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 16 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation4 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (m 2 : ℤ) + (m 5 : ℤ) + (5) * (m 6 : ℤ) + (2) * (m 7 : ℤ) + (4) * (m 8 : ℤ) + (-1) * (m 9 : ℤ) +
      (2) * (m 11 : ℤ) + (m 12 : ℤ) + (6) * (m 13 : ℤ) + (3) * (m 14 : ℤ) + (2) * (m 15 : ℤ) + (10)
      * (m 16 : ℤ) + (18) * (m 17 : ℤ) + (6) * (m 18 : ℤ) + (9) * (m 19 : ℤ) + (3) * (m 21 : ℤ) +
      (7) * (m 22 : ℤ) + (4) * (m 23 : ℤ) + (2) * (m 24 : ℤ) + (12) * (m 25 : ℤ) + (6) * (m 26 : ℤ)
      + (20) * (m 27 : ℤ) + (10) * (m 28 : ℤ) + (27) * (m 29 : ℤ) + (-2) * (m 30 : ℤ) + (-1) * (m 31
      : ℤ) + (m 35 : ℤ) + (2) * (m 36 : ℤ) + (6) * (m 37 : ℤ) + (14) * (m 38 : ℤ) + (22) * (m 39 :
      ℤ) + (30) * (m 40 : ℤ) + (15) * (m 41 : ℤ) + (m 44 : ℤ) + (5) * (m 45 : ℤ) + (2) * (m 46 : ℤ)
      + (4) * (m 47 : ℤ) + (2) * (m 49 : ℤ) + (m 50 : ℤ) = 12 := by
  have hh := h.gram 4
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (0) + ((m 1 : ℤ) * (0) + ((m 2 : ℤ) * (1) + ((m 3 : ℤ) * (0) + ((m 4 : ℤ) * (0)
    + ((m 5 : ℤ) * (1) + ((m 6 : ℤ) * (5) + ((m 7 : ℤ) * (2) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) * (-1)
    + ((m 10 : ℤ) * (0) + ((m 11 : ℤ) * (2) + ((m 12 : ℤ) * (1) + ((m 13 : ℤ) * (6) + ((m 14 : ℤ) *
    (3) + ((m 15 : ℤ) * (2) + ((m 16 : ℤ) * (10) + ((m 17 : ℤ) * (18) + ((m 18 : ℤ) * (6) + ((m 19 :
    ℤ) * (9) + ((m 20 : ℤ) * (0) + ((m 21 : ℤ) * (3) + ((m 22 : ℤ) * (7) + ((m 23 : ℤ) * (4) + ((m
    24 : ℤ) * (2) + ((m 25 : ℤ) * (12) + ((m 26 : ℤ) * (6) + ((m 27 : ℤ) * (20) + ((m 28 : ℤ) * (10)
    + ((m 29 : ℤ) * (27) + ((m 30 : ℤ) * (-2) + ((m 31 : ℤ) * (-1) + ((m 32 : ℤ) * (0) + ((m 33 : ℤ)
    * (0) + ((m 34 : ℤ) * (0) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (2) + ((m 37 : ℤ) * (6) + ((m 38 :
    ℤ) * (14) + ((m 39 : ℤ) * (22) + ((m 40 : ℤ) * (30) + ((m 41 : ℤ) * (15) + ((m 42 : ℤ) * (0) +
    ((m 43 : ℤ) * (0) + ((m 44 : ℤ) * (1) + ((m 45 : ℤ) * (5) + ((m 46 : ℤ) * (2) + ((m 47 : ℤ) *
    (4) + ((m 48 : ℤ) * (0) + ((m 49 : ℤ) * (2) + ((m 50 : ℤ) * (1) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 12 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation5 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (m 0 : ℤ) + (m 2 : ℤ) + (2) * (m 3 : ℤ) + (m 4 : ℤ) + (m 5 : ℤ) + (7) * (m 6 : ℤ) + (m 7 : ℤ) +
      (4) * (m 8 : ℤ) + (m 9 : ℤ) + (3) * (m 10 : ℤ) + (2) * (m 11 : ℤ) + (m 12 : ℤ) + (10) * (m 13
      : ℤ) + (5) * (m 14 : ℤ) + (m 15 : ℤ) + (7) * (m 16 : ℤ) + (21) * (m 17 : ℤ) + (4) * (m 18 : ℤ)
      + (9) * (m 19 : ℤ) + (m 20 : ℤ) + (3) * (m 21 : ℤ) + (13) * (m 22 : ℤ) + (2) * (m 23 : ℤ) + (m
      24 : ℤ) + (10) * (m 25 : ℤ) + (5) * (m 26 : ℤ) + (26) * (m 27 : ℤ) + (13) * (m 28 : ℤ) + (21)
      * (m 29 : ℤ) + (2) * (m 30 : ℤ) + (m 31 : ℤ) + (m 32 : ℤ) + (7) * (m 33 : ℤ) + (m 35 : ℤ) +
      (4) * (m 36 : ℤ) + (3) * (m 37 : ℤ) + (13) * (m 38 : ℤ) + (31) * (m 39 : ℤ) + (26) * (m 40 :
      ℤ) + (13) * (m 41 : ℤ) + (2) * (m 42 : ℤ) + (m 43 : ℤ) + (m 44 : ℤ) + (7) * (m 45 : ℤ) + (m 46
      : ℤ) + (4) * (m 47 : ℤ) + (3) * (m 48 : ℤ) + (2) * (m 49 : ℤ) + (m 50 : ℤ) = 16 := by
  have hh := h.gram 5
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (1) + ((m 1 : ℤ) * (0) + ((m 2 : ℤ) * (1) + ((m 3 : ℤ) * (2) + ((m 4 : ℤ) * (1)
    + ((m 5 : ℤ) * (1) + ((m 6 : ℤ) * (7) + ((m 7 : ℤ) * (1) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) * (1) +
    ((m 10 : ℤ) * (3) + ((m 11 : ℤ) * (2) + ((m 12 : ℤ) * (1) + ((m 13 : ℤ) * (10) + ((m 14 : ℤ) *
    (5) + ((m 15 : ℤ) * (1) + ((m 16 : ℤ) * (7) + ((m 17 : ℤ) * (21) + ((m 18 : ℤ) * (4) + ((m 19 :
    ℤ) * (9) + ((m 20 : ℤ) * (1) + ((m 21 : ℤ) * (3) + ((m 22 : ℤ) * (13) + ((m 23 : ℤ) * (2) + ((m
    24 : ℤ) * (1) + ((m 25 : ℤ) * (10) + ((m 26 : ℤ) * (5) + ((m 27 : ℤ) * (26) + ((m 28 : ℤ) * (13)
    + ((m 29 : ℤ) * (21) + ((m 30 : ℤ) * (2) + ((m 31 : ℤ) * (1) + ((m 32 : ℤ) * (1) + ((m 33 : ℤ) *
    (7) + ((m 34 : ℤ) * (0) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (4) + ((m 37 : ℤ) * (3) + ((m 38 :
    ℤ) * (13) + ((m 39 : ℤ) * (31) + ((m 40 : ℤ) * (26) + ((m 41 : ℤ) * (13) + ((m 42 : ℤ) * (2) +
    ((m 43 : ℤ) * (1) + ((m 44 : ℤ) * (1) + ((m 45 : ℤ) * (7) + ((m 46 : ℤ) * (1) + ((m 47 : ℤ) *
    (4) + ((m 48 : ℤ) * (3) + ((m 49 : ℤ) * (2) + ((m 50 : ℤ) * (1) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 16 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation6 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (m 2 : ℤ) + (m 3 : ℤ) + (6) * (m 6 : ℤ) + (m 7 : ℤ) + (4) * (m 8 : ℤ) + (m 9 : ℤ) + (2) * (m 10
      : ℤ) + (m 11 : ℤ) + (9) * (m 13 : ℤ) + (4) * (m 14 : ℤ) + (6) * (m 16 : ℤ) + (20) * (m 17 : ℤ)
      + (4) * (m 18 : ℤ) + (9) * (m 19 : ℤ) + (m 20 : ℤ) + (2) * (m 21 : ℤ) + (12) * (m 22 : ℤ) + (m
      23 : ℤ) + (9) * (m 25 : ℤ) + (4) * (m 26 : ℤ) + (25) * (m 27 : ℤ) + (12) * (m 28 : ℤ) + (20) *
      (m 29 : ℤ) + (m 30 : ℤ) + (6) * (m 33 : ℤ) + (m 35 : ℤ) + (4) * (m 36 : ℤ) + (2) * (m 37 : ℤ)
      + (12) * (m 38 : ℤ) + (30) * (m 39 : ℤ) + (25) * (m 40 : ℤ) + (12) * (m 41 : ℤ) + (m 42 : ℤ) +
      (6) * (m 45 : ℤ) + (m 46 : ℤ) + (4) * (m 47 : ℤ) + (2) * (m 48 : ℤ) + (m 49 : ℤ) = 12 := by
  have hh := h.gram 6
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (0) + ((m 1 : ℤ) * (0) + ((m 2 : ℤ) * (1) + ((m 3 : ℤ) * (1) + ((m 4 : ℤ) * (0)
    + ((m 5 : ℤ) * (0) + ((m 6 : ℤ) * (6) + ((m 7 : ℤ) * (1) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) * (1) +
    ((m 10 : ℤ) * (2) + ((m 11 : ℤ) * (1) + ((m 12 : ℤ) * (0) + ((m 13 : ℤ) * (9) + ((m 14 : ℤ) *
    (4) + ((m 15 : ℤ) * (0) + ((m 16 : ℤ) * (6) + ((m 17 : ℤ) * (20) + ((m 18 : ℤ) * (4) + ((m 19 :
    ℤ) * (9) + ((m 20 : ℤ) * (1) + ((m 21 : ℤ) * (2) + ((m 22 : ℤ) * (12) + ((m 23 : ℤ) * (1) + ((m
    24 : ℤ) * (0) + ((m 25 : ℤ) * (9) + ((m 26 : ℤ) * (4) + ((m 27 : ℤ) * (25) + ((m 28 : ℤ) * (12)
    + ((m 29 : ℤ) * (20) + ((m 30 : ℤ) * (1) + ((m 31 : ℤ) * (0) + ((m 32 : ℤ) * (0) + ((m 33 : ℤ) *
    (6) + ((m 34 : ℤ) * (0) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (4) + ((m 37 : ℤ) * (2) + ((m 38 :
    ℤ) * (12) + ((m 39 : ℤ) * (30) + ((m 40 : ℤ) * (25) + ((m 41 : ℤ) * (12) + ((m 42 : ℤ) * (1) +
    ((m 43 : ℤ) * (0) + ((m 44 : ℤ) * (0) + ((m 45 : ℤ) * (6) + ((m 46 : ℤ) * (1) + ((m 47 : ℤ) *
    (4) + ((m 48 : ℤ) * (2) + ((m 49 : ℤ) * (1) + ((m 50 : ℤ) * (0) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 12 at hh
  clear h
  omega

set_option maxRecDepth 2048 in
private theorem equation7 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (m 2 : ℤ) + (m 4 : ℤ) + (6) * (m 6 : ℤ) + (m 7 : ℤ) + (4) * (m 8 : ℤ) + (m 9 : ℤ) + (2) * (m 10
      : ℤ) + (m 12 : ℤ) + (8) * (m 13 : ℤ) + (5) * (m 14 : ℤ) + (6) * (m 16 : ℤ) + (20) * (m 17 : ℤ)
      + (4) * (m 18 : ℤ) + (9) * (m 19 : ℤ) + (m 20 : ℤ) + (2) * (m 21 : ℤ) + (12) * (m 22 : ℤ) + (m
      24 : ℤ) + (8) * (m 25 : ℤ) + (5) * (m 26 : ℤ) + (24) * (m 27 : ℤ) + (13) * (m 28 : ℤ) + (20) *
      (m 29 : ℤ) + (m 31 : ℤ) + (6) * (m 33 : ℤ) + (m 35 : ℤ) + (4) * (m 36 : ℤ) + (2) * (m 37 : ℤ)
      + (12) * (m 38 : ℤ) + (30) * (m 39 : ℤ) + (24) * (m 40 : ℤ) + (13) * (m 41 : ℤ) + (m 43 : ℤ) +
      (6) * (m 45 : ℤ) + (m 46 : ℤ) + (4) * (m 47 : ℤ) + (2) * (m 48 : ℤ) + (m 50 : ℤ) = 12 := by
  have hh := h.gram 7
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  change (m 0 : ℤ) * (0) + ((m 1 : ℤ) * (0) + ((m 2 : ℤ) * (1) + ((m 3 : ℤ) * (0) + ((m 4 : ℤ) * (1)
    + ((m 5 : ℤ) * (0) + ((m 6 : ℤ) * (6) + ((m 7 : ℤ) * (1) + ((m 8 : ℤ) * (4) + ((m 9 : ℤ) * (1) +
    ((m 10 : ℤ) * (2) + ((m 11 : ℤ) * (0) + ((m 12 : ℤ) * (1) + ((m 13 : ℤ) * (8) + ((m 14 : ℤ) *
    (5) + ((m 15 : ℤ) * (0) + ((m 16 : ℤ) * (6) + ((m 17 : ℤ) * (20) + ((m 18 : ℤ) * (4) + ((m 19 :
    ℤ) * (9) + ((m 20 : ℤ) * (1) + ((m 21 : ℤ) * (2) + ((m 22 : ℤ) * (12) + ((m 23 : ℤ) * (0) + ((m
    24 : ℤ) * (1) + ((m 25 : ℤ) * (8) + ((m 26 : ℤ) * (5) + ((m 27 : ℤ) * (24) + ((m 28 : ℤ) * (13)
    + ((m 29 : ℤ) * (20) + ((m 30 : ℤ) * (0) + ((m 31 : ℤ) * (1) + ((m 32 : ℤ) * (0) + ((m 33 : ℤ) *
    (6) + ((m 34 : ℤ) * (0) + ((m 35 : ℤ) * (1) + ((m 36 : ℤ) * (4) + ((m 37 : ℤ) * (2) + ((m 38 :
    ℤ) * (12) + ((m 39 : ℤ) * (30) + ((m 40 : ℤ) * (24) + ((m 41 : ℤ) * (13) + ((m 42 : ℤ) * (0) +
    ((m 43 : ℤ) * (1) + ((m 44 : ℤ) * (0) + ((m 45 : ℤ) * (6) + ((m 46 : ℤ) * (1) + ((m 47 : ℤ) *
    (4) + ((m 48 : ℤ) * (2) + ((m 49 : ℤ) * (0) + ((m 50 : ℤ) * (1) + ((0 :
    ℤ)))))))))))))))))))))))))))))))))))))))))))))))))))) = 12 at hh
  clear h
  omega

private theorem principal_bound (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (1 : ℤ) ≤ m 34 := by exact_mod_cast h.principal

private theorem opposite_bound (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    (1 : ℤ) ≤ (m 3 : ℤ) + (m 11 : ℤ) + (m 13 : ℤ) + (m 23 : ℤ) + (m 25 : ℤ) + (m 27 : ℤ) + (m 30 :
      ℤ) + (m 40 : ℤ) + (m 42 : ℤ) + (m 49 : ℤ) := by
  have ho : (1 : ℤ) ≤ ∑ p ∈ oppositeOrbits, (m p : ℤ) := by
    exact_mod_cast h.opposite
  simpa [oppositeOrbits, Finset.sum_insert, Finset.sum_singleton, add_assoc] using ho

/-- A shared bound eliminates coordinates 0, 1, 2, 5, 6, 7, 8, 15, 16, 17, 18, 19, 29, 48. -/
private theorem vanish0 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    : m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 5 = 0 ∧ m 6 = 0 ∧ m 7 = 0 ∧ m 8 = 0 ∧ m 15 = 0 ∧ m 16 = 0 ∧ m
      17 = 0 ∧ m 18 = 0 ∧ m 19 = 0 ∧ m 29 = 0 ∧ m 48 = 0 := by
  have hb : (32) * (m 0 : ℤ) + (16) * (m 1 : ℤ) + (16) * (m 2 : ℤ) + (32) * (m 5 : ℤ) + (32) * (m 6
    : ℤ) + (16) * (m 7 : ℤ) + (16) * (m 8 : ℤ) + (32) * (m 15 : ℤ) + (32) * (m 16 : ℤ) + (32) * (m
    17 : ℤ) + (16) * (m 18 : ℤ) + (16) * (m 19 : ℤ) + (32) * (m 29 : ℤ) + (32) * (m 48 : ℤ) ≤ 0 :=
    by
    linear_combination (norm := (clear * - m; omega)) (1) * (equation0 m h) + (-2) * (equation1 m h)
      + (1) * (equation3 m h) + (-4) * (equation5 m h) + (8) * (equation6 m h) + (-4) * (equation7 m
      h) + (16) * (opposite_bound m h)
  clear h
  omega

/-- A shared bound eliminates coordinates 3, 10, 13, 37, 44, 49, 50. -/
private theorem vanish1 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    : m 3 = 0 ∧ m 10 = 0 ∧ m 13 = 0 ∧ m 37 = 0 ∧ m 44 = 0 ∧ m 49 = 0 ∧ m 50 = 0 := by
  have hb : (256) * (m 0 : ℤ) + (64) * (m 2 : ℤ) + (192) * (m 3 : ℤ) + (96) * (m 4 : ℤ) + (192) * (m
    6 : ℤ) + (48) * (m 8 : ℤ) + (96) * (m 9 : ℤ) + (128) * (m 10 : ℤ) + (128) * (m 13 : ℤ) + (64) *
    (m 14 : ℤ) + (128) * (m 17 : ℤ) + (32) * (m 19 : ℤ) + (16) * (m 20 : ℤ) + (64) * (m 22 : ℤ) +
    (64) * (m 23 : ℤ) + (32) * (m 24 : ℤ) + (64) * (m 27 : ℤ) + (32) * (m 28 : ℤ) + (128) * (m 37 :
    ℤ) + (192) * (m 44 : ℤ) + (48) * (m 46 : ℤ) + (256) * (m 49 : ℤ) + (128) * (m 50 : ℤ) ≤ 112 :=
    by
    linear_combination (norm := (clear * - m; omega)) (5) * (equation0 m h) + (18) * (equation1 m h)
      + (-24) * (equation2 m h) + (9) * (equation3 m h) + (-24) * (equation4 m h) + (4) * (equation5
      m h) + (8) * (equation6 m h) + (4) * (equation7 m h) + (32) * (principal_bound m h)
  clear h
  omega

/-- A shared bound eliminates coordinates 9, 23, 24, 30, 31, 33. -/
private theorem vanish2 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    : m 9 = 0 ∧ m 23 = 0 ∧ m 24 = 0 ∧ m 30 = 0 ∧ m 31 = 0 ∧ m 33 = 0 := by
  have hb : (m 1 : ℤ) + (2) * (m 5 : ℤ) + (m 7 : ℤ) + (4) * (m 9 : ℤ) + (2) * (m 10 : ℤ) + (12) * (m
    15 : ℤ) + (2) * (m 16 : ℤ) + (m 18 : ℤ) + (m 20 : ℤ) + (2) * (m 22 : ℤ) + (8) * (m 23 : ℤ) + (4)
    * (m 24 : ℤ) + (2) * (m 29 : ℤ) + (8) * (m 30 : ℤ) + (4) * (m 31 : ℤ) + (6) * (m 33 : ℤ) + (m 36
    : ℤ) + (6) * (m 37 : ℤ) + (2) * (m 39 : ℤ) + (2) * (m 44 : ℤ) + (m 46 : ℤ) + (2) * (m 48 : ℤ) ≤
    2 := by
    linear_combination (norm := (clear * - m; omega)) (1) * (equation3 m h) + (-2) * (equation4 m h)
      + (1) * (equation6 m h) + (1) * (opposite_bound m h) + (1) * (principal_bound m h)
  clear h
  omega

/-- A shared bound eliminates coordinates 22, 27, 39. -/
private theorem vanish3 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    : m 22 = 0 ∧ m 27 = 0 ∧ m 39 = 0 := by
  have hb : (64) * (m 0 : ℤ) + (24) * (m 2 : ℤ) + (64) * (m 3 : ℤ) + (32) * (m 4 : ℤ) + (96) * (m 6
    : ℤ) + (32) * (m 8 : ℤ) + (48) * (m 9 : ℤ) + (64) * (m 10 : ℤ) + (96) * (m 13 : ℤ) + (48) * (m
    14 : ℤ) + (128) * (m 17 : ℤ) + (40) * (m 19 : ℤ) + (16) * (m 20 : ℤ) + (96) * (m 22 : ℤ) + (128)
    * (m 27 : ℤ) + (64) * (m 28 : ℤ) + (32) * (m 30 : ℤ) + (16) * (m 31 : ℤ) + (64) * (m 33 : ℤ) +
    (24) * (m 36 : ℤ) + (128) * (m 39 : ℤ) + (32) * (m 44 : ℤ) + (32) * (m 49 : ℤ) + (16) * (m 50 :
    ℤ) ≤ 72 := by
    linear_combination (norm := (clear * - m; omega)) (1) * (equation0 m h) + (4) * (equation1 m h)
      + (-8) * (equation2 m h) + (3) * (equation3 m h) + (-16) * (equation4 m h) + (4) * (equation5
      m h) + (8) * (equation6 m h) + (4) * (equation7 m h) + (8) * (principal_bound m h)
  clear h
  omega

/-- A shared bound eliminates coordinates 38, 40, 41, 45. -/
private theorem vanish4 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (z3 : m 3 = 0) (z6 : m 6 = 0) (z10 : m 10 = 0) (z13 : m 13 = 0)
    : m 38 = 0 ∧ m 40 = 0 ∧ m 41 = 0 ∧ m 45 = 0 := by
  have hb : (8) * (m 0 : ℤ) + (32) * (m 1 : ℤ) + (8) * (m 2 : ℤ) + (-32) * (m 3 : ℤ) + (56) * (m 5 :
    ℤ) + (-8) * (m 6 : ℤ) + (28) * (m 7 : ℤ) + (8) * (m 8 : ℤ) + (12) * (m 9 : ℤ) + (-16) * (m 10 :
    ℤ) + (16) * (m 12 : ℤ) + (-32) * (m 13 : ℤ) + (136) * (m 15 : ℤ) + (56) * (m 16 : ℤ) + (8) * (m
    17 : ℤ) + (32) * (m 18 : ℤ) + (16) * (m 19 : ℤ) + (4) * (m 20 : ℤ) + (64) * (m 23 : ℤ) + (48) *
    (m 24 : ℤ) + (16) * (m 25 : ℤ) + (24) * (m 26 : ℤ) + (16) * (m 28 : ℤ) + (88) * (m 29 : ℤ) +
    (64) * (m 30 : ℤ) + (48) * (m 31 : ℤ) + (48) * (m 33 : ℤ) + (4) * (m 35 : ℤ) + (12) * (m 36 : ℤ)
    + (48) * (m 37 : ℤ) + (32) * (m 38 : ℤ) + (48) * (m 39 : ℤ) + (64) * (m 40 : ℤ) + (48) * (m 41 :
    ℤ) + (16) * (m 42 : ℤ) + (24) * (m 43 : ℤ) + (32) * (m 45 : ℤ) + (12) * (m 46 : ℤ) + (16) * (m
    47 : ℤ) + (88) * (m 48 : ℤ) + (16) * (m 50 : ℤ) ≤ 24 := by
    linear_combination (norm := (clear * - m; omega)) (1) * (equation0 m h) + (-5) * (equation1 m h)
      + (6) * (equation2 m h) + (8) * (equation3 m h) + (-10) * (equation4 m h) + (-10) * (equation5
      m h) + (14) * (equation7 m h) + (4) * (opposite_bound m h) + (4) * (principal_bound m h)
  clear h
  simp only [z3, z6, z10, z13, Int.natCast_zero, mul_zero] at hb
  omega

/-- A shared bound eliminates coordinates 25. -/
private theorem vanish5 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (z1 : m 1 = 0) (z2 : m 2 = 0) (z5 : m 5 = 0) (z6 : m 6 = 0)
    : m 25 = 0 := by
  have hb : (-2) * (m 1 : ℤ) + (-2) * (m 2 : ℤ) + (-4) * (m 5 : ℤ) + (-4) * (m 6 : ℤ) + (2) * (m 9 :
    ℤ) + (8) * (m 15 : ℤ) + (8) * (m 16 : ℤ) + (8) * (m 17 : ℤ) + (6) * (m 18 : ℤ) + (6) * (m 19 :
    ℤ) + (4) * (m 21 : ℤ) + (4) * (m 22 : ℤ) + (16) * (m 23 : ℤ) + (8) * (m 24 : ℤ) + (16) * (m 25 :
    ℤ) + (8) * (m 26 : ℤ) + (16) * (m 27 : ℤ) + (8) * (m 28 : ℤ) + (36) * (m 29 : ℤ) + (2) * (m 35 :
    ℤ) + (2) * (m 36 : ℤ) + (24) * (m 37 : ℤ) + (24) * (m 38 : ℤ) + (24) * (m 39 : ℤ) + (48) * (m 40
    : ℤ) + (24) * (m 41 : ℤ) + (12) * (m 44 : ℤ) + (12) * (m 45 : ℤ) + (8) * (m 46 : ℤ) + (8) * (m
    47 : ℤ) + (16) * (m 49 : ℤ) + (8) * (m 50 : ℤ) ≤ 14 := by
    linear_combination (norm := (clear * - m; omega)) (1) * (equation1 m h) + (1) * (equation3 m h)
      + (2) * (principal_bound m h)
  clear h
  simp only [z1, z2, z5, z6, Int.natCast_zero, mul_zero] at hb
  omega

/-- A shared bound eliminates coordinates 26, 43. -/
private theorem vanish6 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (z3 : m 3 = 0) (z6 : m 6 = 0) (z9 : m 9 = 0) (z10 : m 10 = 0) (z13 : m 13 = 0) (z22 : m 22 = 0)
    : m 26 = 0 ∧ m 43 = 0 := by
  have hb : (128) * (m 0 : ℤ) + (208) * (m 1 : ℤ) + (72) * (m 2 : ℤ) + (-192) * (m 3 : ℤ) + (16) *
    (m 4 : ℤ) + (352) * (m 5 : ℤ) + (-32) * (m 6 : ℤ) + (176) * (m 7 : ℤ) + (64) * (m 8 : ℤ) + (-16)
    * (m 9 : ℤ) + (-160) * (m 10 : ℤ) + (112) * (m 12 : ℤ) + (-224) * (m 13 : ℤ) + (640) * (m 15 :
    ℤ) + (352) * (m 16 : ℤ) + (64) * (m 17 : ℤ) + (208) * (m 18 : ℤ) + (120) * (m 19 : ℤ) + (-64) *
    (m 22 : ℤ) + (256) * (m 23 : ℤ) + (240) * (m 24 : ℤ) + (128) * (m 25 : ℤ) + (176) * (m 26 : ℤ) +
    (112) * (m 28 : ℤ) + (608) * (m 29 : ℤ) + (224) * (m 30 : ℤ) + (224) * (m 31 : ℤ) + (160) * (m
    33 : ℤ) + (32) * (m 35 : ℤ) + (56) * (m 36 : ℤ) + (224) * (m 37 : ℤ) + (256) * (m 38 : ℤ) +
    (288) * (m 39 : ℤ) + (512) * (m 40 : ℤ) + (368) * (m 41 : ℤ) + (128) * (m 42 : ℤ) + (176) * (m
    43 : ℤ) + (256) * (m 45 : ℤ) + (80) * (m 46 : ℤ) + (128) * (m 47 : ℤ) + (608) * (m 48 : ℤ) +
    (96) * (m 49 : ℤ) + (160) * (m 50 : ℤ) ≤ 136 := by
    linear_combination (norm := (clear * - m; omega)) (9) * (equation0 m h) + (-32) * (equation1 m
      h) + (40) * (equation2 m h) + (31) * (equation3 m h) + (-16) * (equation4 m h) + (-76) *
      (equation5 m h) + (-24) * (equation6 m h) + (100) * (equation7 m h) + (8) * (principal_bound m
      h)
  clear h
  simp only [z3, z6, z9, z10, z13, z22, Int.natCast_zero, mul_zero] at hb
  omega

/-- A shared bound eliminates coordinates 28. -/
private theorem vanish7 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    : m 28 = 0 := by
  have hb : (64) * (m 0 : ℤ) + (48) * (m 1 : ℤ) + (32) * (m 2 : ℤ) + (64) * (m 5 : ℤ) + (64) * (m 6
    : ℤ) + (32) * (m 7 : ℤ) + (48) * (m 8 : ℤ) + (16) * (m 9 : ℤ) + (64) * (m 13 : ℤ) + (32) * (m 14
    : ℤ) + (64) * (m 15 : ℤ) + (64) * (m 16 : ℤ) + (192) * (m 17 : ℤ) + (48) * (m 18 : ℤ) + (96) *
    (m 19 : ℤ) + (16) * (m 20 : ℤ) + (128) * (m 22 : ℤ) + (64) * (m 25 : ℤ) + (32) * (m 26 : ℤ) +
    (256) * (m 27 : ℤ) + (128) * (m 28 : ℤ) + (192) * (m 29 : ℤ) + (64) * (m 30 : ℤ) + (32) * (m 31
    : ℤ) + (128) * (m 33 : ℤ) + (16) * (m 35 : ℤ) + (64) * (m 36 : ℤ) + (128) * (m 38 : ℤ) + (384) *
    (m 39 : ℤ) + (256) * (m 40 : ℤ) + (128) * (m 41 : ℤ) + (64) * (m 42 : ℤ) + (32) * (m 43 : ℤ) +
    (128) * (m 45 : ℤ) + (16) * (m 46 : ℤ) + (64) * (m 47 : ℤ) + (192) * (m 48 : ℤ) + (64) * (m 49 :
    ℤ) + (32) * (m 50 : ℤ) ≤ 112 := by
    linear_combination (norm := (clear * - m; omega)) (3) * (equation0 m h) + (-6) * (equation1 m h)
      + (8) * (equation2 m h) + (3) * (equation3 m h) + (-8) * (equation4 m h) + (-20) * (equation5
      m h) + (24) * (equation6 m h) + (12) * (equation7 m h)
  clear h
  omega

/-- A shared bound eliminates coordinates 12. -/
private theorem vanish8 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (z3 : m 3 = 0) (z10 : m 10 = 0) (z13 : m 13 = 0) (z22 : m 22 = 0) (z27 : m 27 = 0)
    : m 12 = 0 := by
  have hb : (64) * (m 0 : ℤ) + (68) * (m 1 : ℤ) + (36) * (m 2 : ℤ) + (-48) * (m 3 : ℤ) + (8) * (m 4
    : ℤ) + (128) * (m 5 : ℤ) + (32) * (m 6 : ℤ) + (64) * (m 7 : ℤ) + (32) * (m 8 : ℤ) + (4) * (m 9 :
    ℤ) + (-32) * (m 10 : ℤ) + (32) * (m 12 : ℤ) + (-64) * (m 13 : ℤ) + (224) * (m 15 : ℤ) + (128) *
    (m 16 : ℤ) + (32) * (m 17 : ℤ) + (68) * (m 18 : ℤ) + (36) * (m 19 : ℤ) + (-32) * (m 22 : ℤ) +
    (80) * (m 23 : ℤ) + (72) * (m 24 : ℤ) + (16) * (m 25 : ℤ) + (40) * (m 26 : ℤ) + (-48) * (m 27 :
    ℤ) + (8) * (m 28 : ℤ) + (160) * (m 29 : ℤ) + (64) * (m 30 : ℤ) + (64) * (m 31 : ℤ) + (32) * (m
    33 : ℤ) + (4) * (m 35 : ℤ) + (4) * (m 36 : ℤ) + (64) * (m 37 : ℤ) + (32) * (m 38 : ℤ) + (64) *
    (m 40 : ℤ) + (64) * (m 41 : ℤ) + (16) * (m 42 : ℤ) + (40) * (m 43 : ℤ) + (32) * (m 45 : ℤ) +
    (16) * (m 46 : ℤ) + (16) * (m 47 : ℤ) + (160) * (m 48 : ℤ) + (32) * (m 50 : ℤ) ≤ 20 := by
    linear_combination (norm := (clear * - m; omega)) (3) * (equation0 m h) + (-10) * (equation1 m
      h) + (8) * (equation2 m h) + (11) * (equation3 m h) + (-8) * (equation4 m h) + (-20) *
      (equation5 m h) + (20) * (equation7 m h) + (24) * (opposite_bound m h) + (4) *
      (principal_bound m h)
  clear h
  simp only [z3, z10, z13, z22, z27, Int.natCast_zero, mul_zero] at hb
  omega

/-- A shared bound eliminates coordinates 42. -/
private theorem vanish9 (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (z8 : m 8 = 0) (z13 : m 13 = 0) (z16 : m 16 = 0) (z17 : m 17 = 0) (z18 : m 18 = 0) (z19 : m 19 =
      0) (z22 : m 22 = 0) (z23 : m 23 = 0) (z25 : m 25 = 0) (z26 : m 26 = 0) (z27 : m 27 = 0) (z28 :
      m 28 = 0) (z29 : m 29 = 0) (z37 : m 37 = 0) (z38 : m 38 = 0) (z39 : m 39 = 0) (z40 : m 40 = 0)
      (z41 : m 41 = 0)
    : m 42 = 0 := by
  have hb : (108) * (m 0 : ℤ) + (36) * (m 1 : ℤ) + (20) * (m 2 : ℤ) + (24) * (m 3 : ℤ) + (28) * (m 4
    : ℤ) + (72) * (m 5 : ℤ) + (24) * (m 6 : ℤ) + (8) * (m 7 : ℤ) + (-8) * (m 8 : ℤ) + (12) * (m 10 :
    ℤ) + (16) * (m 12 : ℤ) + (-32) * (m 13 : ℤ) + (36) * (m 15 : ℤ) + (-12) * (m 16 : ℤ) + (-60) *
    (m 17 : ℤ) + (-20) * (m 18 : ℤ) + (-36) * (m 19 : ℤ) + (-16) * (m 22 : ℤ) + (-24) * (m 23 : ℤ) +
    (4) * (m 24 : ℤ) + (-56) * (m 25 : ℤ) + (-12) * (m 26 : ℤ) + (-88) * (m 27 : ℤ) + (-28) * (m 28
    : ℤ) + (-96) * (m 29 : ℤ) + (32) * (m 30 : ℤ) + (32) * (m 31 : ℤ) + (28) * (m 32 : ℤ) + (44) *
    (m 33 : ℤ) + (-12) * (m 37 : ℤ) + (-28) * (m 38 : ℤ) + (-44) * (m 39 : ℤ) + (-112) * (m 40 : ℤ)
    + (-40) * (m 41 : ℤ) + (56) * (m 42 : ℤ) + (44) * (m 43 : ℤ) + (40) * (m 44 : ℤ) + (56) * (m 45
    : ℤ) + (156) * (m 48 : ℤ) + (80) * (m 49 : ℤ) + (56) * (m 50 : ℤ) ≤ 28 := by
    linear_combination (norm := (clear * - m; omega)) (3) * (equation0 m h) + (-3) * (equation1 m h)
      + (4) * (equation2 m h) + (-4) * (equation4 m h) + (12) * (equation5 m h) + (-12) * (equation6
      m h) + (20) * (opposite_bound m h)
  clear h
  simp only [z8, z13, z16, z17, z18, z19, z22, z23, z25, z26, z27, z28, z29, z37, z38, z39, z40,
    z41, Int.natCast_zero, mul_zero] at hb
  omega

private def liveIndices : Finset (Fin 51) := {4, 11, 14, 20, 21, 32, 34, 35, 36, 46, 47}

private def Supported (m : Fin 51 → ℕ) : Prop :=
  ∀ p, p ∉ liveIndices → m p = 0

private theorem support (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    Supported m := by
  obtain ⟨z0, z1, z2, z5, z6, z7, z8, z15, z16, z17, z18, z19, z29, z48⟩ := vanish0 m h
  obtain ⟨z3, z10, z13, z37, z44, z49, z50⟩ := vanish1 m h
  obtain ⟨z9, z23, z24, z30, z31, z33⟩ := vanish2 m h
  obtain ⟨z22, z27, z39⟩ := vanish3 m h
  obtain ⟨z38, z40, z41, z45⟩ := vanish4 m h z3 z6 z10 z13
  obtain z25 := vanish5 m h z1 z2 z5 z6
  obtain ⟨z26, z43⟩ := vanish6 m h z3 z6 z9 z10 z13 z22
  obtain z28 := vanish7 m h
  obtain z12 := vanish8 m h z3 z10 z13 z22 z27
  obtain z42 := vanish9 m h z8 z13 z16 z17 z18 z19 z22 z23 z25 z26 z27 z28 z29 z37 z38 z39 z40 z41
  clear h
  intro p hp
  fin_cases p
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact (hp (by decide)).elim
  · exact z5
  · exact z6
  · exact z7
  · exact z8
  · exact z9
  · exact z10
  · exact (hp (by decide)).elim
  · exact z12
  · exact z13
  · exact (hp (by decide)).elim
  · exact z15
  · exact z16
  · exact z17
  · exact z18
  · exact z19
  · exact (hp (by decide)).elim
  · exact (hp (by decide)).elim
  · exact z22
  · exact z23
  · exact z24
  · exact z25
  · exact z26
  · exact z27
  · exact z28
  · exact z29
  · exact z30
  · exact z31
  · exact (hp (by decide)).elim
  · exact z33
  · exact (hp (by decide)).elim
  · exact (hp (by decide)).elim
  · exact (hp (by decide)).elim
  · exact z37
  · exact z38
  · exact z39
  · exact z40
  · exact z41
  · exact z42
  · exact z43
  · exact z44
  · exact z45
  · exact (hp (by decide)).elim
  · exact (hp (by decide)).elim
  · exact z48
  · exact z49
  · exact z50

private def restrictCounts (m : Fin 51 → ℕ) : Fin 11 → ℕ :=
  ![m 4, m 11, m 14, m 20, m 21, m 32, m 34, m 35, m 36, m 46, m 47]

private def expandCounts (r : Fin 11 → ℕ) (p : Fin 51) : ℕ :=
  if p = 4 then r 0 else
  if p = 11 then r 1 else
  if p = 14 then r 2 else
  if p = 20 then r 3 else
  if p = 21 then r 4 else
  if p = 32 then r 5 else
  if p = 34 then r 6 else
  if p = 35 then r 7 else
  if p = 36 then r 8 else
  if p = 46 then r 9 else
  if p = 47 then r 10 else 0

private theorem reconstruct (m : Fin 51 → ℕ) (hz : Supported m) :
    m = expandCounts (restrictCounts m) := by
  funext p
  fin_cases p
  · exact hz 0 (by decide)
  · exact hz 1 (by decide)
  · exact hz 2 (by decide)
  · exact hz 3 (by decide)
  · rfl
  · exact hz 5 (by decide)
  · exact hz 6 (by decide)
  · exact hz 7 (by decide)
  · exact hz 8 (by decide)
  · exact hz 9 (by decide)
  · exact hz 10 (by decide)
  · rfl
  · exact hz 12 (by decide)
  · exact hz 13 (by decide)
  · rfl
  · exact hz 15 (by decide)
  · exact hz 16 (by decide)
  · exact hz 17 (by decide)
  · exact hz 18 (by decide)
  · exact hz 19 (by decide)
  · rfl
  · rfl
  · exact hz 22 (by decide)
  · exact hz 23 (by decide)
  · exact hz 24 (by decide)
  · exact hz 25 (by decide)
  · exact hz 26 (by decide)
  · exact hz 27 (by decide)
  · exact hz 28 (by decide)
  · exact hz 29 (by decide)
  · exact hz 30 (by decide)
  · exact hz 31 (by decide)
  · rfl
  · exact hz 33 (by decide)
  · rfl
  · rfl
  · rfl
  · exact hz 37 (by decide)
  · exact hz 38 (by decide)
  · exact hz 39 (by decide)
  · exact hz 40 (by decide)
  · exact hz 41 (by decide)
  · exact hz 42 (by decide)
  · exact hz 43 (by decide)
  · exact hz 44 (by decide)
  · exact hz 45 (by decide)
  · rfl
  · rfl
  · exact hz 48 (by decide)
  · exact hz 49 (by decide)
  · exact hz 50 (by decide)

private def smallModel : Fin 4 → Fin 11 → ℕ :=
  ![![1, 1, 0, 1, 2, 0, 1, 2, 1, 0, 0], ![0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 2,
    0, 0, 0, 1], ![0, 1, 1, 1, 1, 1, 2, 4, 0, 0, 0]]

private theorem model_expand0 : modelCounts 0 = expandCounts (smallModel 0) := by
  decide

private theorem model_expand1 : modelCounts 1 = expandCounts (smallModel 1) := by
  decide

private theorem model_expand2 : modelCounts 2 = expandCounts (smallModel 2) := by
  decide

set_option maxRecDepth 2048 in
private theorem model_expand3 : modelCounts 3 = expandCounts (smallModel 3) := by
  decide

private theorem model_expand (v : Fin 4) :
    modelCounts v = expandCounts (smallModel v) := by
  fin_cases v
  · exact model_expand0
  · exact model_expand1
  · exact model_expand2
  · exact model_expand3

private structure ResidualEquations (r : Fin 11 → ℕ) : Prop where
  eq0 : (8) * (r 0 : ℤ) + (4) * (r 1 : ℤ) + (2) * (r 2 : ℤ) + (4) * (r 5 : ℤ) + (r 6 : ℤ) + (r 7 :
    ℤ) + (r 8 : ℤ) + (4) * (r 9 : ℤ) + (4) * (r 10 : ℤ) = 16
  eq1 : (-4) * (r 1 : ℤ) + (-2) * (r 2 : ℤ) + (r 6 : ℤ) + (r 7 : ℤ) + (r 8 : ℤ) + (4) * (r 9 : ℤ) +
    (4) * (r 10 : ℤ) = 0
  eq2 : (-2) * (r 0 : ℤ) + (-2) * (r 1 : ℤ) + (-3) * (r 2 : ℤ) + (r 5 : ℤ) + (r 7 : ℤ) + (2) * (r 8
    : ℤ) + (2) * (r 9 : ℤ) + (4) * (r 10 : ℤ) = 0
  eq3 : (4) * (r 1 : ℤ) + (2) * (r 2 : ℤ) + (4) * (r 4 : ℤ) + (r 6 : ℤ) + (r 7 : ℤ) + (r 8 : ℤ) +
    (4) * (r 9 : ℤ) + (4) * (r 10 : ℤ) = 16
  eq4 : (2) * (r 1 : ℤ) + (3) * (r 2 : ℤ) + (3) * (r 4 : ℤ) + (r 7 : ℤ) + (2) * (r 8 : ℤ) + (2) * (r
    9 : ℤ) + (4) * (r 10 : ℤ) = 12
  eq5 : (r 0 : ℤ) + (2) * (r 1 : ℤ) + (5) * (r 2 : ℤ) + (r 3 : ℤ) + (3) * (r 4 : ℤ) + (r 5 : ℤ) + (r
    7 : ℤ) + (4) * (r 8 : ℤ) + (r 9 : ℤ) + (4) * (r 10 : ℤ) = 16
  eq6 : (r 1 : ℤ) + (4) * (r 2 : ℤ) + (r 3 : ℤ) + (2) * (r 4 : ℤ) + (r 7 : ℤ) + (4) * (r 8 : ℤ) + (r
    9 : ℤ) + (4) * (r 10 : ℤ) = 12
  eq7 : (r 0 : ℤ) + (5) * (r 2 : ℤ) + (r 3 : ℤ) + (2) * (r 4 : ℤ) + (r 7 : ℤ) + (4) * (r 8 : ℤ) + (r
    9 : ℤ) + (4) * (r 10 : ℤ) = 12
  principal : (1 : ℤ) ≤ r 6
  opposite : (1 : ℤ) ≤ r 1

private theorem residual_equations (m : Fin 51 → ℕ) (h : MultiplicityConstraints m)
    (hz : Supported m) : ResidualEquations (restrictCounts m) := by
  have z0 : m 0 = 0 := hz 0 (by decide)
  have z1 : m 1 = 0 := hz 1 (by decide)
  have z2 : m 2 = 0 := hz 2 (by decide)
  have z3 : m 3 = 0 := hz 3 (by decide)
  have z5 : m 5 = 0 := hz 5 (by decide)
  have z6 : m 6 = 0 := hz 6 (by decide)
  have z7 : m 7 = 0 := hz 7 (by decide)
  have z8 : m 8 = 0 := hz 8 (by decide)
  have z9 : m 9 = 0 := hz 9 (by decide)
  have z10 : m 10 = 0 := hz 10 (by decide)
  have z12 : m 12 = 0 := hz 12 (by decide)
  have z13 : m 13 = 0 := hz 13 (by decide)
  have z15 : m 15 = 0 := hz 15 (by decide)
  have z16 : m 16 = 0 := hz 16 (by decide)
  have z17 : m 17 = 0 := hz 17 (by decide)
  have z18 : m 18 = 0 := hz 18 (by decide)
  have z19 : m 19 = 0 := hz 19 (by decide)
  have z22 : m 22 = 0 := hz 22 (by decide)
  have z23 : m 23 = 0 := hz 23 (by decide)
  have z24 : m 24 = 0 := hz 24 (by decide)
  have z25 : m 25 = 0 := hz 25 (by decide)
  have z26 : m 26 = 0 := hz 26 (by decide)
  have z27 : m 27 = 0 := hz 27 (by decide)
  have z28 : m 28 = 0 := hz 28 (by decide)
  have z29 : m 29 = 0 := hz 29 (by decide)
  have z30 : m 30 = 0 := hz 30 (by decide)
  have z31 : m 31 = 0 := hz 31 (by decide)
  have z33 : m 33 = 0 := hz 33 (by decide)
  have z37 : m 37 = 0 := hz 37 (by decide)
  have z38 : m 38 = 0 := hz 38 (by decide)
  have z39 : m 39 = 0 := hz 39 (by decide)
  have z40 : m 40 = 0 := hz 40 (by decide)
  have z41 : m 41 = 0 := hz 41 (by decide)
  have z42 : m 42 = 0 := hz 42 (by decide)
  have z43 : m 43 = 0 := hz 43 (by decide)
  have z44 : m 44 = 0 := hz 44 (by decide)
  have z45 : m 45 = 0 := hz 45 (by decide)
  have z48 : m 48 = 0 := hz 48 (by decide)
  have z49 : m 49 = 0 := hz 49 (by decide)
  have z50 : m 50 = 0 := hz 50 (by decide)
  constructor
  · change (8) * (m 4 : ℤ) + (4) * (m 11 : ℤ) + (2) * (m 14 : ℤ) + (4) * (m 32 : ℤ) + (m 34 : ℤ) +
    (m 35 : ℤ) + (m 36 : ℤ) + (4) * (m 46 : ℤ) + (4) * (m 47 : ℤ) = 16
    simpa only [z0, z1, z2, z3, z5, z6, z7, z8, z9, z10, z12, z13, z15, z16, z17, z18, z19, z30,
      z31, z33, z37, z38, z39, z40, z41, z42, z43, z44, z45, z48, z49, z50, Int.natCast_zero,
      mul_zero, zero_add, add_zero] using equation0 m h
  · change (-4) * (m 11 : ℤ) + (-2) * (m 14 : ℤ) + (m 34 : ℤ) + (m 35 : ℤ) + (m 36 : ℤ) + (4) * (m
    46 : ℤ) + (4) * (m 47 : ℤ) = 0
    simpa only [z1, z2, z5, z6, z7, z8, z9, z12, z13, z15, z16, z17, z18, z19, z30, z31, z37, z38,
      z39, z40, z41, z44, z45, z49, z50, Int.natCast_zero, mul_zero, zero_add, add_zero] using
      equation1 m h
  · change (-2) * (m 4 : ℤ) + (-2) * (m 11 : ℤ) + (-3) * (m 14 : ℤ) + (m 32 : ℤ) + (m 35 : ℤ) + (2)
    * (m 36 : ℤ) + (2) * (m 46 : ℤ) + (4) * (m 47 : ℤ) = 0
    simpa only [z0, z2, z3, z5, z6, z7, z8, z9, z10, z12, z13, z15, z16, z17, z18, z19, z30, z31,
      z33, z37, z38, z39, z40, z41, z42, z43, z44, z45, z48, z49, z50, Int.natCast_zero, mul_zero,
      zero_add, add_zero] using equation2 m h
  · change (4) * (m 11 : ℤ) + (2) * (m 14 : ℤ) + (4) * (m 21 : ℤ) + (m 34 : ℤ) + (m 35 : ℤ) + (m 36
    : ℤ) + (4) * (m 46 : ℤ) + (4) * (m 47 : ℤ) = 16
    simpa only [z1, z2, z5, z6, z7, z8, z9, z12, z13, z15, z16, z17, z18, z19, z22, z23, z24, z25,
      z26, z27, z28, z29, z30, z31, z37, z38, z39, z40, z41, z44, z45, z49, z50, Int.natCast_zero,
      mul_zero, zero_add, add_zero] using equation3 m h
  · change (2) * (m 11 : ℤ) + (3) * (m 14 : ℤ) + (3) * (m 21 : ℤ) + (m 35 : ℤ) + (2) * (m 36 : ℤ) +
    (2) * (m 46 : ℤ) + (4) * (m 47 : ℤ) = 12
    simpa only [z2, z5, z6, z7, z8, z9, z12, z13, z15, z16, z17, z18, z19, z22, z23, z24, z25, z26,
      z27, z28, z29, z30, z31, z37, z38, z39, z40, z41, z44, z45, z49, z50, Int.natCast_zero,
      mul_zero, zero_add, add_zero] using equation4 m h
  · change (m 4 : ℤ) + (2) * (m 11 : ℤ) + (5) * (m 14 : ℤ) + (m 20 : ℤ) + (3) * (m 21 : ℤ) + (m 32 :
    ℤ) + (m 35 : ℤ) + (4) * (m 36 : ℤ) + (m 46 : ℤ) + (4) * (m 47 : ℤ) = 16
    simpa only [z0, z2, z3, z5, z6, z7, z8, z9, z10, z12, z13, z15, z16, z17, z18, z19, z22, z23,
      z24, z25, z26, z27, z28, z29, z30, z31, z33, z37, z38, z39, z40, z41, z42, z43, z44, z45, z48,
      z49, z50, Int.natCast_zero, mul_zero, zero_add, add_zero] using equation5 m h
  · change (m 11 : ℤ) + (4) * (m 14 : ℤ) + (m 20 : ℤ) + (2) * (m 21 : ℤ) + (m 35 : ℤ) + (4) * (m 36
    : ℤ) + (m 46 : ℤ) + (4) * (m 47 : ℤ) = 12
    simpa only [z2, z3, z6, z7, z8, z9, z10, z13, z16, z17, z18, z19, z22, z23, z25, z26, z27, z28,
      z29, z30, z33, z37, z38, z39, z40, z41, z42, z45, z48, z49, Int.natCast_zero, mul_zero,
      zero_add, add_zero] using equation6 m h
  · change (m 4 : ℤ) + (5) * (m 14 : ℤ) + (m 20 : ℤ) + (2) * (m 21 : ℤ) + (m 35 : ℤ) + (4) * (m 36 :
    ℤ) + (m 46 : ℤ) + (4) * (m 47 : ℤ) = 12
    simpa only [z2, z6, z7, z8, z9, z10, z12, z13, z16, z17, z18, z19, z22, z24, z25, z26, z27, z28,
      z29, z31, z33, z37, z38, z39, z40, z41, z43, z45, z48, z50, Int.natCast_zero, mul_zero,
      zero_add, add_zero] using equation7 m h
  · exact principal_bound m h
  · change (1 : ℤ) ≤ m 11
    simpa only [z3, z13, z23, z25, z27, z30, z40, z42, z49, Int.natCast_zero, zero_add, add_zero]
      using opposite_bound m h

private theorem normal_relation0 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 1 = 1 := by
  have hh : (48 : ℤ) * ((r 1 : ℤ)) = 48 := by
    linear_combination (norm := (clear * - r; omega)) (3) * h.eq0 + (-10) * h.eq1 + (4) * h.eq2 +
      (7) * h.eq3 + (-4) * h.eq4 + (-16) * h.eq5 + (16) * h.eq6
  clear h
  omega

private theorem normal_relation1 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 0 + r 2 = 1 := by
  have hh : (16 : ℤ) * ((r 0 : ℤ) + (r 2 : ℤ)) = 16 := by
    linear_combination (norm := (clear * - r; omega)) (1) * h.eq0 + (2) * h.eq1 + (-4) * h.eq2 +
      (-3) * h.eq3 + (4) * h.eq4
  clear h
  omega

private theorem normal_relation2 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 4 = r 0 + 1 := by
  have hh : (48 : ℤ) * ((-1) * (r 0 : ℤ) + (r 4 : ℤ)) = 48 := by
    linear_combination (norm := (clear * - r; omega)) (-9) * h.eq0 + (2) * h.eq1 + (4) * h.eq2 + (7)
      * h.eq3 + (-4) * h.eq4 + (32) * h.eq5 + (-32) * h.eq6
  clear h
  omega

private theorem normal_relation3 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 0 + r 5 = 1 := by
  have hh : (48 : ℤ) * ((r 0 : ℤ) + (r 5 : ℤ)) = 48 := by
    linear_combination (norm := (clear * - r; omega)) (3) * h.eq0 + (2) * h.eq1 + (4) * h.eq2 + (-5)
      * h.eq3 + (-4) * h.eq4 + (32) * h.eq5 + (-32) * h.eq6
  clear h
  omega

private theorem normal_relation4 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 6 + 2 * r 0 + 2 * r 9 = r 8 + 2 := by
  have hh : (8 : ℤ) * ((2) * (r 0 : ℤ) + (r 6 : ℤ) + (-1) * (r 8 : ℤ) + (2) * (r 9 : ℤ)) = 16 := by
    linear_combination (norm := (clear * - r; omega)) (1) * h.eq0 + (4) * h.eq1 + (-4) * h.eq2 + (3)
      * h.eq3 + (-4) * h.eq4
  clear h
  omega

private theorem normal_relation5 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 3 + r 6 + r 8 + r 9 = 3 := by
  have hh : (48 : ℤ) * ((r 3 : ℤ) + (r 6 : ℤ) + (r 8 : ℤ) + (r 9 : ℤ)) = 144 := by
    linear_combination (norm := (clear * - r; omega)) (-3) * h.eq0 + (10) * h.eq1 + (-4) * h.eq2 +
      (41) * h.eq3 + (-92) * h.eq4 + (16) * h.eq5 + (32) * h.eq6
  clear h
  omega

private theorem normal_relation6 (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    r 7 + 2 * r 8 + 2 * r 9 + 4 * r 10 = 4 := by
  have hh : (12 : ℤ) * ((r 7 : ℤ) + (2) * (r 8 : ℤ) + (2) * (r 9 : ℤ) + (4) * (r 10 : ℤ)) = 48 := by
    linear_combination (norm := (clear * - r; omega)) (3) * h.eq0 + (-1) * h.eq1 + (4) * h.eq2 +
      (-2) * h.eq3 + (8) * h.eq4 + (-16) * h.eq5 + (16) * h.eq6
  clear h
  omega

private structure NormalForm (r : Fin 11 → ℕ) : Prop where
  eq0 : r 1 = 1
  eq1 : r 0 + r 2 = 1
  eq2 : r 4 = r 0 + 1
  eq3 : r 0 + r 5 = 1
  eq4 : r 6 + 2 * r 0 + 2 * r 9 = r 8 + 2
  eq5 : r 3 + r 6 + r 8 + r 9 = 3
  eq6 : r 7 + 2 * r 8 + 2 * r 9 + 4 * r 10 = 4
  principal : 1 ≤ r 6

private theorem normal_form (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    NormalForm r := by
  refine ⟨normal_relation0 r h, normal_relation1 r h, normal_relation2 r h, normal_relation3 r h,
    normal_relation4 r h, normal_relation5 r h, normal_relation6 r h, ?_⟩
  exact_mod_cast h.principal

private theorem residual_case0 (r : Fin 11 → ℕ) (h : NormalForm r)
    (h4 : r 0 ≠ 0) : r = smallModel 0 := by
  rcases h with ⟨he0, he1, he2, he3, he4, he5, he6, hp⟩
  have ha : r 0 = 1 := by omega
  have hj : r 9 = 0 := by omega
  have hk : r 10 = 0 := by omega
  have hv : r 0 = 1 ∧ r 1 = 1 ∧ r 2 = 0 ∧ r 3 = 1 ∧ r 4 = 2 ∧ r 5 = 0 ∧ r 6 = 1 ∧ r 7 = 2 ∧ r 8 = 1
    ∧ r 9 = 0 ∧ r 10 = 0 := by omega
  rcases hv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
  funext i
  fin_cases i
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

private theorem residual_case1 (r : Fin 11 → ℕ) (h : NormalForm r)
    (h4 : r 0 = 0) (h46 : r 9 ≠ 0) : r = smallModel 1 := by
  rcases h with ⟨he0, he1, he2, he3, he4, he5, he6, hp⟩
  have hv : r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 1 ∧ r 3 = 0 ∧ r 4 = 1 ∧ r 5 = 1 ∧ r 6 = 1 ∧ r 7 = 0 ∧ r 8 = 1
    ∧ r 9 = 1 ∧ r 10 = 0 := by omega
  rcases hv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
  funext i
  fin_cases i
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

private theorem residual_case2 (r : Fin 11 → ℕ) (h : NormalForm r)
    (h4 : r 0 = 0) (h46 : r 9 = 0) (h47 : r 10 ≠ 0) : r = smallModel 2 := by
  rcases h with ⟨he0, he1, he2, he3, he4, he5, he6, hp⟩
  have hv : r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 1 ∧ r 3 = 1 ∧ r 4 = 1 ∧ r 5 = 1 ∧ r 6 = 2 ∧ r 7 = 0 ∧ r 8 = 0
    ∧ r 9 = 0 ∧ r 10 = 1 := by omega
  rcases hv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
  funext i
  fin_cases i
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

private theorem residual_case3 (r : Fin 11 → ℕ) (h : NormalForm r)
    (h4 : r 0 = 0) (h46 : r 9 = 0) (h47 : r 10 = 0) : r = smallModel 3 := by
  rcases h with ⟨he0, he1, he2, he3, he4, he5, he6, hp⟩
  have hv : r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 1 ∧ r 3 = 1 ∧ r 4 = 1 ∧ r 5 = 1 ∧ r 6 = 2 ∧ r 7 = 4 ∧ r 8 = 0
    ∧ r 9 = 0 ∧ r 10 = 0 := by omega
  rcases hv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
  funext i
  fin_cases i
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

private theorem solve_residual (r : Fin 11 → ℕ) (h : ResidualEquations r) :
    ∃ v : Fin 4, r = smallModel v := by
  have hn := normal_form r h
  by_cases h4 : r 0 = 0
  · by_cases h46 : r 9 = 0
    · by_cases h47 : r 10 = 0
      · exact ⟨3, residual_case3 r hn h4 h46 h47⟩
      · exact ⟨2, residual_case2 r hn h4 h46 h47⟩
    · exact ⟨1, residual_case1 r hn h4 h46⟩
  · exact ⟨0, residual_case0 r hn h4⟩

/-- The eight Gram equations and the two positivity conditions classify all
multiplicities per distinct orbit row as the four Table I models S–V. -/
public theorem classify_factored (m : Fin 51 → ℕ) (h : MultiplicityConstraints m) :
    ∃ v : Fin 4, m = modelCounts v := by
  have hz := support m h
  obtain ⟨v, hv⟩ := solve_residual (restrictCounts m) (residual_equations m h hz)
  refine ⟨v, ?_⟩
  calc
    m = expandCounts (restrictCounts m) := reconstruct m hz
    _ = expandCounts (smallModel v) := congrArg expandCounts hv
    _ = modelCounts v := (model_expand v).symm

end Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows
