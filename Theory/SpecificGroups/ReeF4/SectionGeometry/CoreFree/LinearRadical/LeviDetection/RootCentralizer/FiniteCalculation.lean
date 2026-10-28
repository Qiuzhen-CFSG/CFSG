module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Operators

/-!
# A finite matrix calculation for linear Levi detection

In the certified numbered Cartan-plus-root basis, four binary operators have
only diagonal matrices in their degree-preserving common centralizer. There
are two possible diagonal values: one on coordinates 15, 19, 23 and one on
the other 49 coordinates. The proof consists of explicit commutation equations
and characteristic-two linear elimination, checked over an arbitrary ring.

The tables in this module are numerical data. Identifying them with the four
actual degree-one root operators is a separate obligation; no such comparison
is assumed by their definitions or asserted by the finite calculation.

Source: the standard F4 lattice in `TraceValues.Operators`, and the root-defined
Levi of GLS3 Theorem 2.6.5(e,g), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer

open Matrix

/-- The middle-root degree in the numbered basis. -/
def degree : Fin 52 → ℤ :=
  ![0, 0, 0, 0, -5, 5, -2, 2, -2, 2, -1, 1, -7, -3, 3, 7, -7, -3, 3, 7, -6, -4, 4, 6, -4, 0, 0, 4, -3, -1, 1, 3, -3, -1, 1, 3, -5, -4, -3, -2, -3, -2, -1, 0, 0, 1, 2, 3, 2, 3, 4, 5]

/-- Supports of the four binary test operators, ordered as roots
0100, 0010, 1100, 0011. Their comparison with actual operators is separate. -/
def operatorSupport : Fin 4 → List (Fin 52 × Fin 52)
  | 0 => [(1, 33), (9, 11), (10, 8), (17, 21), (19, 23), (20, 16), (22, 18), (25, 29), (27, 31), (28, 24), (30, 26), (34, 0), (38, 37), (42, 41), (46, 45), (50, 49)]
  | 1 => [(2, 10), (4, 20), (5, 22), (6, 28), (7, 30), (8, 32), (9, 34), (11, 1), (11, 3), (37, 36), (39, 38), (41, 40), (43, 42), (45, 44), (47, 46), (49, 48), (51, 50)]
  | 2 => [(0, 29), (1, 29), (7, 11), (10, 6), (13, 21), (15, 23), (20, 12), (22, 14), (26, 33), (27, 35), (30, 0), (30, 1), (32, 24), (34, 25), (40, 37), (42, 39), (48, 45), (50, 47)]
  | _ => [(2, 42), (3, 42), (5, 50), (6, 38), (8, 40), (11, 43), (36, 20), (37, 4), (39, 17), (41, 13), (44, 10), (45, 1), (45, 2), (45, 3), (46, 34), (47, 9), (48, 30), (49, 7), (51, 27)]

/-- Binary matrices interpreted over any coefficient ring. -/
def testOperator {F : Type*} [Semiring F] (k : Fin 4) : Matrix (Fin 52) (Fin 52) F :=
  ((operatorSupport k).map fun p => Matrix.single p.1 p.2 1).sum

/-- The exceptional diagonal value occurs on three positive long roots. -/
def exceptional (i : Fin 52) : Bool := i == 15 || i == 19 || i == 23

/-- The diagonal shape forced by the four commutation equations. -/
def diagonalShape {F : Type*} [Zero F] (a b : F) : Matrix (Fin 52) (Fin 52) F :=
  Matrix.diagonal fun i => if exceptional i then b else a

private def positions : List (Fin 52 × Fin 52) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 25), (0, 26), (0, 43), (0, 44), (1, 0), (1, 1), (1, 2), (1, 3), (1, 25), (1, 26), (1, 43), (1, 44), (2, 0), (2, 1), (2, 2), (2, 3), (2, 25), (2, 26), (2, 43), (2, 44), (3, 0), (3, 1), (3, 2), (3, 3), (3, 25), (3, 26), (3, 43), (3, 44), (4, 4), (4, 36), (5, 5), (5, 51), (6, 6), (6, 8), (6, 39), (6, 41), (7, 7), (7, 9), (7, 46), (7, 48), (8, 6), (8, 8), (8, 39), (8, 41), (9, 7), (9, 9), (9, 46), (9, 48), (10, 10), (10, 29), (10, 33), (10, 42), (11, 11), (11, 30), (11, 34), (11, 45), (12, 12), (12, 16), (13, 13), (13, 17), (13, 28), (13, 32), (13, 38), (13, 40), (14, 14), (14, 18), (14, 31), (14, 35), (14, 47), (14, 49), (15, 15), (15, 19), (16, 12), (16, 16), (17, 13), (17, 17), (17, 28), (17, 32), (17, 38), (17, 40), (18, 14), (18, 18), (18, 31), (18, 35), (18, 47), (18, 49), (19, 15), (19, 19), (20, 20), (21, 21), (21, 24), (21, 37), (22, 22), (22, 27), (22, 50), (23, 23), (24, 21), (24, 24), (24, 37), (25, 0), (25, 1), (25, 2), (25, 3), (25, 25), (25, 26), (25, 43), (25, 44), (26, 0), (26, 1), (26, 2), (26, 3), (26, 25), (26, 26), (26, 43), (26, 44), (27, 22), (27, 27), (27, 50), (28, 13), (28, 17), (28, 28), (28, 32), (28, 38), (28, 40), (29, 10), (29, 29), (29, 33), (29, 42), (30, 11), (30, 30), (30, 34), (30, 45), (31, 14), (31, 18), (31, 31), (31, 35), (31, 47), (31, 49), (32, 13), (32, 17), (32, 28), (32, 32), (32, 38), (32, 40), (33, 10), (33, 29), (33, 33), (33, 42), (34, 11), (34, 30), (34, 34), (34, 45), (35, 14), (35, 18), (35, 31), (35, 35), (35, 47), (35, 49), (36, 4), (36, 36), (37, 21), (37, 24), (37, 37), (38, 13), (38, 17), (38, 28), (38, 32), (38, 38), (38, 40), (39, 6), (39, 8), (39, 39), (39, 41), (40, 13), (40, 17), (40, 28), (40, 32), (40, 38), (40, 40), (41, 6), (41, 8), (41, 39), (41, 41), (42, 10), (42, 29), (42, 33), (42, 42), (43, 0), (43, 1), (43, 2), (43, 3), (43, 25), (43, 26), (43, 43), (43, 44), (44, 0), (44, 1), (44, 2), (44, 3), (44, 25), (44, 26), (44, 43), (44, 44), (45, 11), (45, 30), (45, 34), (45, 45), (46, 7), (46, 9), (46, 46), (46, 48), (47, 14), (47, 18), (47, 31), (47, 35), (47, 47), (47, 49), (48, 7), (48, 9), (48, 46), (48, 48), (49, 14), (49, 18), (49, 31), (49, 35), (49, 47), (49, 49), (50, 22), (50, 27), (50, 50), (51, 5), (51, 51)]

set_option maxRecDepth 4000 in
private theorem positions_complete (i j : Fin 52) :
    degree i = degree j → (i, j) ∈ positions := by
  revert i j
  decide +kernel

open Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.Cartan.FieldSeparation.TraceValues

set_option maxHeartbeats 2000000 in
/-- The numerical grading is the published grading on the actual F4 lattice. -/
theorem degree_eq_basisDegree (i : Fin 52) : degree i = basisDegree (basisEquiv i) := by
  fin_cases i
  · change 0 = basisDegree (.inl (typeF4RootPairing_baseEquiv 0))
    simp
  · change 0 = basisDegree (.inl (typeF4RootPairing_baseEquiv 1))
    simp
  · change 0 = basisDegree (.inl (typeF4RootPairing_baseEquiv 2))
    simp
  · change 0 = basisDegree (.inl (typeF4RootPairing_baseEquiv 3))
    simp
  · change (-5 : ℤ) = rootDegree (root 0)
    have h : (rootDegree (root 0) : ℝ) = -5 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (5 : ℤ) = rootDegree (root 1)
    have h : (rootDegree (root 1) : ℝ) = 5 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-2 : ℤ) = rootDegree (root 2)
    have h : (rootDegree (root 2) : ℝ) = -2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (2 : ℤ) = rootDegree (root 3)
    have h : (rootDegree (root 3) : ℝ) = 2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-2 : ℤ) = rootDegree (root 4)
    have h : (rootDegree (root 4) : ℝ) = -2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (2 : ℤ) = rootDegree (root 5)
    have h : (rootDegree (root 5) : ℝ) = 2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-1 : ℤ) = rootDegree (root 6)
    have h : (rootDegree (root 6) : ℝ) = -1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (1 : ℤ) = rootDegree (root 7)
    have h : (rootDegree (root 7) : ℝ) = 1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-7 : ℤ) = rootDegree (root 8)
    have h : (rootDegree (root 8) : ℝ) = -7 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 9)
    have h : (rootDegree (root 9) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 10)
    have h : (rootDegree (root 10) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (7 : ℤ) = rootDegree (root 11)
    have h : (rootDegree (root 11) : ℝ) = 7 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-7 : ℤ) = rootDegree (root 12)
    have h : (rootDegree (root 12) : ℝ) = -7 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 13)
    have h : (rootDegree (root 13) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 14)
    have h : (rootDegree (root 14) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (7 : ℤ) = rootDegree (root 15)
    have h : (rootDegree (root 15) : ℝ) = 7 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-6 : ℤ) = rootDegree (root 16)
    have h : (rootDegree (root 16) : ℝ) = -6 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-4 : ℤ) = rootDegree (root 17)
    have h : (rootDegree (root 17) : ℝ) = -4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (4 : ℤ) = rootDegree (root 18)
    have h : (rootDegree (root 18) : ℝ) = 4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (6 : ℤ) = rootDegree (root 19)
    have h : (rootDegree (root 19) : ℝ) = 6 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-4 : ℤ) = rootDegree (root 20)
    have h : (rootDegree (root 20) : ℝ) = -4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (0 : ℤ) = rootDegree (root 21)
    have h : (rootDegree (root 21) : ℝ) = 0 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (0 : ℤ) = rootDegree (root 22)
    have h : (rootDegree (root 22) : ℝ) = 0 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (4 : ℤ) = rootDegree (root 23)
    have h : (rootDegree (root 23) : ℝ) = 4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 24)
    have h : (rootDegree (root 24) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-1 : ℤ) = rootDegree (root 25)
    have h : (rootDegree (root 25) : ℝ) = -1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (1 : ℤ) = rootDegree (root 26)
    have h : (rootDegree (root 26) : ℝ) = 1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 27)
    have h : (rootDegree (root 27) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 28)
    have h : (rootDegree (root 28) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-1 : ℤ) = rootDegree (root 29)
    have h : (rootDegree (root 29) : ℝ) = -1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (1 : ℤ) = rootDegree (root 30)
    have h : (rootDegree (root 30) : ℝ) = 1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 31)
    have h : (rootDegree (root 31) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-5 : ℤ) = rootDegree (root 32)
    have h : (rootDegree (root 32) : ℝ) = -5 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-4 : ℤ) = rootDegree (root 33)
    have h : (rootDegree (root 33) : ℝ) = -4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 34)
    have h : (rootDegree (root 34) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-2 : ℤ) = rootDegree (root 35)
    have h : (rootDegree (root 35) : ℝ) = -2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-3 : ℤ) = rootDegree (root 36)
    have h : (rootDegree (root 36) : ℝ) = -3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-2 : ℤ) = rootDegree (root 37)
    have h : (rootDegree (root 37) : ℝ) = -2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (-1 : ℤ) = rootDegree (root 38)
    have h : (rootDegree (root 38) : ℝ) = -1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (0 : ℤ) = rootDegree (root 39)
    have h : (rootDegree (root 39) : ℝ) = 0 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (0 : ℤ) = rootDegree (root 40)
    have h : (rootDegree (root 40) : ℝ) = 0 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (1 : ℤ) = rootDegree (root 41)
    have h : (rootDegree (root 41) : ℝ) = 1 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (2 : ℤ) = rootDegree (root 42)
    have h : (rootDegree (root 42) : ℝ) = 2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 43)
    have h : (rootDegree (root 43) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (2 : ℤ) = rootDegree (root 44)
    have h : (rootDegree (root 44) : ℝ) = 2 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (3 : ℤ) = rootDegree (root 45)
    have h : (rootDegree (root 45) : ℝ) = 3 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (4 : ℤ) = rootDegree (root 46)
    have h : (rootDegree (root 46) : ℝ) = 4 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h
  · change (5 : ℤ) = rootDegree (root 47)
    have h : (rootDegree (root 47) : ℝ) = 5 := by
      rw [rootDegree_eq]
      norm_num [root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
    symm
    exact_mod_cast h

/-- The four test roots in the actual, certified F₄ root enumeration. Their
simple-root labels are 0100, 0010, 1100 and 0011, respectively. -/
noncomputable def testRoot (k : Fin 4) : Theory.AlgebraicGroup.F4Chevalley.Root :=
  root (![30, 7, 26, 41] k)

/-- Each test root belongs to the degree-one layer. -/
theorem testRoot_degree (k : Fin 4) : rootDegree (testRoot k) = 1 := by
  have h : (rootDegree (testRoot k) : ℝ) = 1 := by
    rw [rootDegree_eq]
    fin_cases k <;>
      norm_num [testRoot, root, realCoord, coord, typeF4SimpleCoefficient,
        Matrix.cons_val_two, Matrix.cons_val_three]
  exact_mod_cast h

variable {F : Type*} [CommRing F] [CharP F 2]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- Exact centralizer computation over an arbitrary ring of characteristic two. -/
theorem eq_diagonalShape_of_commute (A : Matrix (Fin 52) (Fin 52) F)
    (hd : ∀ i j, degree i ≠ degree j → A i j = 0)
    (hc : ∀ k : Fin 4, Commute A (testOperator k)) :
    A = diagonalShape (A 0 0) (A 15 15) := by
  have h0 : A 0 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 0 29) (hc 0).eq
  have h1 : A 0 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 0 33) (hc 0).eq
  have h2 : 0 = A 33 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 10) (hc 0).eq
  have h3 : A 1 25 = A 33 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 29) (hc 0).eq
  have h4 : A 1 1 = A 33 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 33) (hc 0).eq
  have h5 : 0 = A 33 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 42) (hc 0).eq
  have h6 : A 2 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 29) (hc 0).eq
  have h7 : A 2 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 33) (hc 0).eq
  have h8 : A 3 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 29) (hc 0).eq
  have h9 : A 3 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 33) (hc 0).eq
  have h10 : A 7 9 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 11) (hc 0).eq
  have h11 : A 7 46 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 45) (hc 0).eq
  have h12 : A 9 9 = A 11 11 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 11) (hc 0).eq
  have h13 : 0 = A 11 30 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 30) (hc 0).eq
  have h14 : 0 = A 11 34 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 34) (hc 0).eq
  have h15 : A 9 46 = A 11 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 45) (hc 0).eq
  have h16 : 0 = A 8 6 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 6) (hc 0).eq
  have h17 : A 10 10 = A 8 8 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 8) (hc 0).eq
  have h18 : 0 = A 8 39 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 39) (hc 0).eq
  have h19 : A 10 42 = A 8 41 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 41) (hc 0).eq
  have h20 : A 13 17 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 21) (hc 0).eq
  have h21 : A 13 28 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 24) (hc 0).eq
  have h22 : A 13 38 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 37) (hc 0).eq
  have h23 : A 15 19 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 15 23) (hc 0).eq
  have h24 : A 17 17 = A 21 21 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 21) (hc 0).eq
  have h25 : A 17 28 = A 21 24 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 24) (hc 0).eq
  have h26 : A 17 38 = A 21 37 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 37) (hc 0).eq
  have h27 : A 19 19 = A 23 23 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 19 23) (hc 0).eq
  have h28 : 0 = A 16 12 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 20 12) (hc 0).eq
  have h29 : A 20 20 = A 16 16 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 20 16) (hc 0).eq
  have h30 : 0 = A 18 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 14) (hc 0).eq
  have h31 : A 22 22 = A 18 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 18) (hc 0).eq
  have h32 : A 22 27 = A 18 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 31) (hc 0).eq
  have h33 : 0 = A 18 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 35) (hc 0).eq
  have h34 : 0 = A 18 47 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 47) (hc 0).eq
  have h35 : A 22 50 = A 18 49 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 49) (hc 0).eq
  have h36 : 0 = A 29 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 10) (hc 0).eq
  have h37 : A 25 25 = A 29 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 29) (hc 0).eq
  have h38 : A 25 1 = A 29 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 33) (hc 0).eq
  have h39 : 0 = A 29 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 42) (hc 0).eq
  have h40 : A 26 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 26 29) (hc 0).eq
  have h41 : A 26 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 26 33) (hc 0).eq
  have h42 : 0 = A 31 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 14) (hc 0).eq
  have h43 : A 27 22 = A 31 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 18) (hc 0).eq
  have h44 : A 27 27 = A 31 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 31) (hc 0).eq
  have h45 : 0 = A 31 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 35) (hc 0).eq
  have h46 : 0 = A 31 47 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 47) (hc 0).eq
  have h47 : A 27 50 = A 31 49 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 49) (hc 0).eq
  have h48 : A 28 17 = A 24 21 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 28 21) (hc 0).eq
  have h49 : A 28 28 = A 24 24 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 28 24) (hc 0).eq
  have h50 : A 28 38 = A 24 37 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 28 37) (hc 0).eq
  have h51 : A 30 34 = A 26 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 0) (hc 0).eq
  have h52 : 0 = A 26 2 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 2) (hc 0).eq
  have h53 : 0 = A 26 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 3) (hc 0).eq
  have h54 : A 30 30 = A 26 26 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 26) (hc 0).eq
  have h55 : 0 = A 26 43 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 43) (hc 0).eq
  have h56 : 0 = A 26 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 44) (hc 0).eq
  have h57 : A 32 17 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 32 21) (hc 0).eq
  have h58 : A 32 28 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 32 24) (hc 0).eq
  have h59 : A 32 38 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 32 37) (hc 0).eq
  have h60 : A 34 34 = A 0 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 0) (hc 0).eq
  have h61 : 0 = A 0 2 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 2) (hc 0).eq
  have h62 : 0 = A 0 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 3) (hc 0).eq
  have h63 : A 34 30 = A 0 26 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 26) (hc 0).eq
  have h64 : 0 = A 0 43 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 43) (hc 0).eq
  have h65 : 0 = A 0 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 44) (hc 0).eq
  have h66 : A 38 17 = A 37 21 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 38 21) (hc 0).eq
  have h67 : A 38 28 = A 37 24 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 38 24) (hc 0).eq
  have h68 : A 38 38 = A 37 37 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 38 37) (hc 0).eq
  have h69 : A 40 17 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 40 21) (hc 0).eq
  have h70 : A 40 28 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 40 24) (hc 0).eq
  have h71 : A 40 38 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 40 37) (hc 0).eq
  have h72 : 0 = A 41 6 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 42 6) (hc 0).eq
  have h73 : A 42 10 = A 41 8 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 42 8) (hc 0).eq
  have h74 : 0 = A 41 39 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 42 39) (hc 0).eq
  have h75 : A 42 42 = A 41 41 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 42 41) (hc 0).eq
  have h76 : A 43 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 29) (hc 0).eq
  have h77 : A 43 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 33) (hc 0).eq
  have h78 : A 44 25 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 44 29) (hc 0).eq
  have h79 : A 44 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 44 33) (hc 0).eq
  have h80 : A 45 34 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 0) (hc 0).eq
  have h81 : A 45 30 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 26) (hc 0).eq
  have h82 : A 46 9 = A 45 11 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 46 11) (hc 0).eq
  have h83 : A 46 46 = A 45 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 46 45) (hc 0).eq
  have h84 : A 48 9 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 48 11) (hc 0).eq
  have h85 : A 48 46 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 48 45) (hc 0).eq
  have h86 : 0 = A 49 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 14) (hc 0).eq
  have h87 : A 50 22 = A 49 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 18) (hc 0).eq
  have h88 : A 50 27 = A 49 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 31) (hc 0).eq
  have h89 : 0 = A 49 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 35) (hc 0).eq
  have h90 : 0 = A 49 47 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 47) (hc 0).eq
  have h91 : A 50 50 = A 49 49 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 49) (hc 0).eq
  have h92 : A 1 2 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 10) (hc 1).eq
  have h93 : A 1 43 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 42) (hc 1).eq
  have h94 : A 2 2 = A 10 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 10) (hc 1).eq
  have h95 : 0 = A 10 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 29) (hc 1).eq
  have h96 : 0 = A 10 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 33) (hc 1).eq
  have h97 : A 2 43 = A 10 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 42) (hc 1).eq
  have h98 : A 3 2 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 10) (hc 1).eq
  have h99 : A 3 43 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 42) (hc 1).eq
  have h100 : A 4 4 = A 20 20 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 4 20) (hc 1).eq
  have h101 : A 5 5 = A 22 22 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 5 22) (hc 1).eq
  have h102 : 0 = A 22 27 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 5 27) (hc 1).eq
  have h103 : A 5 51 = A 22 50 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 5 50) (hc 1).eq
  have h104 : 0 = A 28 13 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 13) (hc 1).eq
  have h105 : 0 = A 28 17 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 17) (hc 1).eq
  have h106 : A 6 6 = A 28 28 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 28) (hc 1).eq
  have h107 : A 6 8 = A 28 32 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 32) (hc 1).eq
  have h108 : A 6 39 = A 28 38 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 38) (hc 1).eq
  have h109 : A 6 41 = A 28 40 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 40) (hc 1).eq
  have h110 : 0 = A 30 11 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 11) (hc 1).eq
  have h111 : A 7 7 = A 30 30 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 30) (hc 1).eq
  have h112 : A 7 9 = A 30 34 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 34) (hc 1).eq
  have h113 : 0 = A 30 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 45) (hc 1).eq
  have h114 : 0 = A 32 13 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 8 13) (hc 1).eq
  have h115 : A 8 8 = A 32 32 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 8 32) (hc 1).eq
  have h116 : A 8 41 = A 32 40 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 8 40) (hc 1).eq
  have h117 : 0 = A 34 11 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 11) (hc 1).eq
  have h118 : A 9 7 = A 34 30 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 30) (hc 1).eq
  have h119 : A 9 9 = A 34 34 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 34) (hc 1).eq
  have h120 : 0 = A 34 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 45) (hc 1).eq
  have h121 : 0 = A 1 0 + A 3 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 0) (hc 1).eq
  have h122 : A 11 11 = A 1 1 + A 3 1 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 1) (hc 1).eq
  have h123 : A 11 11 = A 1 3 + A 3 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 3) (hc 1).eq
  have h124 : 0 = A 1 25 + A 3 25 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 25) (hc 1).eq
  have h125 : 0 = A 1 26 + A 3 26 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 26) (hc 1).eq
  have h126 : A 11 45 = A 1 44 + A 3 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 44) (hc 1).eq
  have h127 : A 14 47 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 14 46) (hc 1).eq
  have h128 : A 14 49 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 14 48) (hc 1).eq
  have h129 : A 18 49 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 18 48) (hc 1).eq
  have h130 : A 21 37 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 21 36) (hc 1).eq
  have h131 : A 24 37 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 24 36) (hc 1).eq
  have h132 : A 25 2 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 10) (hc 1).eq
  have h133 : A 25 43 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 42) (hc 1).eq
  have h134 : A 31 49 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 31 48) (hc 1).eq
  have h135 : A 35 47 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 35 46) (hc 1).eq
  have h136 : A 35 49 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 35 48) (hc 1).eq
  have h137 : A 36 4 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 36 20) (hc 1).eq
  have h138 : A 37 37 = A 36 36 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 37 36) (hc 1).eq
  have h139 : 0 = A 38 13 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 13) (hc 1).eq
  have h140 : 0 = A 38 17 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 17) (hc 1).eq
  have h141 : A 39 6 = A 38 28 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 28) (hc 1).eq
  have h142 : A 39 8 = A 38 32 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 32) (hc 1).eq
  have h143 : A 39 39 = A 38 38 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 38) (hc 1).eq
  have h144 : A 39 41 = A 38 40 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 40) (hc 1).eq
  have h145 : 0 = A 40 13 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 41 13) (hc 1).eq
  have h146 : A 41 8 = A 40 32 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 41 32) (hc 1).eq
  have h147 : A 41 41 = A 40 40 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 41 40) (hc 1).eq
  have h148 : A 43 2 = A 42 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 10) (hc 1).eq
  have h149 : 0 = A 42 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 29) (hc 1).eq
  have h150 : 0 = A 42 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 33) (hc 1).eq
  have h151 : A 43 43 = A 42 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 42) (hc 1).eq
  have h152 : A 44 2 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 44 10) (hc 1).eq
  have h153 : A 44 43 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 44 42) (hc 1).eq
  have h154 : 0 = A 44 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 0) (hc 1).eq
  have h155 : A 45 11 = A 44 1 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 1) (hc 1).eq
  have h156 : A 45 11 = A 44 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 3) (hc 1).eq
  have h157 : 0 = A 44 26 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 26) (hc 1).eq
  have h158 : A 45 45 = A 44 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 45 44) (hc 1).eq
  have h159 : A 46 7 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 46 30) (hc 1).eq
  have h160 : A 47 47 = A 46 46 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 47 46) (hc 1).eq
  have h161 : A 47 49 = A 46 48 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 47 48) (hc 1).eq
  have h162 : A 48 7 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 48 30) (hc 1).eq
  have h163 : A 49 49 = A 48 48 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 49 48) (hc 1).eq
  have h164 : A 51 5 = A 50 22 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 51 22) (hc 1).eq
  have h165 : 0 = A 50 27 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 51 27) (hc 1).eq
  have h166 : A 51 51 = A 50 50 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 51 50) (hc 1).eq
  have h167 : A 0 0 + A 0 1 = A 29 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 0 29) (hc 2).eq
  have h168 : A 0 26 = A 29 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 0 33) (hc 2).eq
  have h169 : A 1 0 + A 1 1 = A 29 29 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 29) (hc 2).eq
  have h170 : A 1 26 = A 29 33 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 1 33) (hc 2).eq
  have h171 : A 2 0 + A 2 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 29) (hc 2).eq
  have h172 : A 2 26 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 33) (hc 2).eq
  have h173 : A 3 26 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 33) (hc 2).eq
  have h174 : A 7 7 = A 11 11 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 11) (hc 2).eq
  have h175 : A 7 48 = A 11 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 7 45) (hc 2).eq
  have h176 : A 9 48 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 9 45) (hc 2).eq
  have h177 : A 10 10 = A 6 6 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 6) (hc 2).eq
  have h178 : 0 = A 6 8 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 8) (hc 2).eq
  have h179 : A 10 42 = A 6 39 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 39) (hc 2).eq
  have h180 : 0 = A 6 41 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 10 41) (hc 2).eq
  have h181 : A 13 13 = A 21 21 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 21) (hc 2).eq
  have h182 : A 13 32 = A 21 24 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 24) (hc 2).eq
  have h183 : A 13 40 = A 21 37 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 13 37) (hc 2).eq
  have h184 : A 15 15 = A 23 23 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 15 23) (hc 2).eq
  have h185 : A 17 13 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 21) (hc 2).eq
  have h186 : A 17 32 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 24) (hc 2).eq
  have h187 : A 17 40 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 17 37) (hc 2).eq
  have h188 : A 19 15 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 19 23) (hc 2).eq
  have h189 : A 20 20 = A 12 12 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 20 12) (hc 2).eq
  have h190 : 0 = A 12 16 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 20 16) (hc 2).eq
  have h191 : A 22 22 = A 14 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 14) (hc 2).eq
  have h192 : 0 = A 14 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 18) (hc 2).eq
  have h193 : 0 = A 14 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 31) (hc 2).eq
  have h194 : A 22 27 = A 14 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 22 35) (hc 2).eq
  have h195 : A 25 0 + A 25 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 29) (hc 2).eq
  have h196 : A 25 26 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 25 33) (hc 2).eq
  have h197 : A 27 22 = A 35 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 14) (hc 2).eq
  have h198 : 0 = A 35 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 18) (hc 2).eq
  have h199 : 0 = A 35 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 31) (hc 2).eq
  have h200 : A 27 27 = A 35 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 27 35) (hc 2).eq
  have h201 : 0 = A 0 3 + A 1 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 3) (hc 2).eq
  have h202 : 0 = A 0 44 + A 1 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 30 44) (hc 2).eq
  have h203 : 0 = A 25 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 3) (hc 2).eq
  have h204 : 0 = A 25 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 34 44) (hc 2).eq
  have h205 : A 38 32 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 38 24) (hc 2).eq
  have h206 : A 38 40 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 38 37) (hc 2).eq
  have h207 : A 40 32 = A 37 24 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 40 24) (hc 2).eq
  have h208 : A 40 40 = A 37 37 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 40 37) (hc 2).eq
  have h209 : A 43 0 + A 43 1 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 29) (hc 2).eq
  have h210 : A 43 26 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 43 33) (hc 2).eq
  have h211 : A 46 48 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 46 45) (hc 2).eq
  have h212 : A 48 48 = A 45 45 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 48 45) (hc 2).eq
  have h213 : A 50 22 = A 47 14 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 14) (hc 2).eq
  have h214 : 0 = A 47 18 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 18) (hc 2).eq
  have h215 : 0 = A 47 31 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 31) (hc 2).eq
  have h216 : A 50 27 = A 47 35 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 50 35) (hc 2).eq
  have h217 : A 2 44 = A 42 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 10) (hc 3).eq
  have h218 : A 2 2 + A 2 3 = A 42 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 2 42) (hc 3).eq
  have h219 : A 3 44 = A 42 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 10) (hc 3).eq
  have h220 : A 3 2 + A 3 3 = A 42 42 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 3 42) (hc 3).eq
  have h221 : A 4 36 = 0 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 4 20) (hc 3).eq
  have h222 : 0 = A 50 22 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 5 22) (hc 3).eq
  have h223 : A 5 5 = A 50 50 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 5 50) (hc 3).eq
  have h224 : 0 = A 38 28 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 28) (hc 3).eq
  have h225 : A 6 6 = A 38 38 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 6 38) (hc 3).eq
  have h226 : A 11 45 = A 43 3 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 3) (hc 3).eq
  have h227 : 0 = A 43 44 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 11 44) (hc 3).eq
  have h228 : A 36 36 = A 20 20 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 36 20) (hc 3).eq
  have h229 : A 39 39 = A 17 17 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 17) (hc 3).eq
  have h230 : 0 = A 17 28 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 39 28) (hc 3).eq
  have h231 : A 44 44 = A 10 10 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 44 10) (hc 3).eq
  have h232 : 0 = A 27 22 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 51 22) (hc 3).eq
  have h233 : A 51 51 = A 27 27 := by
    simpa [testOperator, operatorSupport, Matrix.mul_add, Matrix.add_mul]
      using congrArg (fun B : Matrix (Fin 52) (Fin 52) F => B 51 27) (hc 3).eq
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have e0 : A 0 0 = A 0 0 := rfl
  have e1 : A 0 1 = 0 := by linear_combination h1
  have e2 : A 0 2 = 0 := by linear_combination h61 + A 0 2 * htwo
  have e3 : A 0 3 = 0 := by linear_combination h62 + A 0 3 * htwo
  have e4 : A 0 25 = 0 := by linear_combination h0
  have e5 : A 0 26 = 0 := by linear_combination h125 + h168 + h170 + h173 + A 29 33 * htwo
  have e6 : A 0 43 = 0 := by linear_combination h64 + A 0 43 * htwo
  have e7 : A 0 44 = 0 := by linear_combination h65 + A 0 44 * htwo
  have e8 : A 1 0 = 0 := by linear_combination h1 + h9 + h12 + h60 + h119 + h122 + h167 + h169 - A 0 1 * htwo - A 9 9 * htwo + A 29 29 * htwo
  have e9 : A 1 1 = A 0 0 := by linear_combination h9 + h12 + h60 + h119 + h122 + A 1 1 * htwo - A 9 9 * htwo
  have e10 : A 1 2 = 0 := by linear_combination h92
  have e11 : A 1 3 = 0 := by linear_combination h62 + h201 + A 1 3 * htwo + A 0 3 * htwo
  have e12 : A 1 25 = 0 := by linear_combination h8 + h124 + A 1 25 * htwo
  have e13 : A 1 26 = 0 := by linear_combination h125 + h173 + A 1 26 * htwo
  have e14 : A 1 43 = 0 := by linear_combination h93
  have e15 : A 1 44 = 0 := by linear_combination h65 + h202 + A 1 44 * htwo + A 0 44 * htwo
  have e16 : A 2 0 = 0 := by linear_combination h7 + h171 - A 2 1 * htwo
  have e17 : A 2 1 = 0 := by linear_combination h7
  have e18 : A 2 2 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h94 + h98 + h119 + h123 + h147 + h177 + h201 + h208 + h220 + h225 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e19 : A 2 3 = 0 := by linear_combination h68 + h75 + h94 + h147 + h177 + h208 + h218 + h225 + A 37 37 * htwo - A 2 2 * htwo
  have e20 : A 2 25 = 0 := by linear_combination h6
  have e21 : A 2 26 = 0 := by linear_combination h172
  have e22 : A 2 43 = 0 := by linear_combination h50 + h97 + h108 + h131 + h179
  have e23 : A 2 44 = 0 := by linear_combination h67 + h73 + h146 + h207 + h217 + h224 + A 37 24 * htwo
  have e24 : A 3 0 = 0 := by linear_combination h1 + h9 + h12 + h60 + h119 + h121 + h122 + h167 + h169 + A 3 0 * htwo - A 0 1 * htwo - A 9 9 * htwo + A 29 29 * htwo
  have e25 : A 3 1 = 0 := by linear_combination h9
  have e26 : A 3 2 = 0 := by linear_combination h98
  have e27 : A 3 3 = A 0 0 := by linear_combination h12 + h60 + h62 + h119 + h123 + h201 + A 3 3 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 1 3 * htwo
  have e28 : A 3 25 = 0 := by linear_combination h8
  have e29 : A 3 26 = 0 := by linear_combination h173
  have e30 : A 3 43 = 0 := by linear_combination h99
  have e31 : A 3 44 = 0 := by linear_combination h67 + h73 + h146 + h207 + h219 + h224 + A 37 24 * htwo
  have e32 : A 4 4 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h100 + h119 + h123 + h138 + h147 + h201 + h208 + h220 + h228 - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 20 20 * htwo + A 1 3 * htwo
  have e33 : A 4 36 = 0 := by linear_combination h221
  have e34 : A 5 5 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h177 + h201 + h208 + h212 + h220 + h223 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e35 : A 5 51 = 0 := by linear_combination h35 + h103 + h129
  have e36 : A 6 6 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h201 + h208 + h220 + h225 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e37 : A 6 8 = 0 := by linear_combination h178 + A 6 8 * htwo
  have e38 : A 6 39 = 0 := by linear_combination h50 + h108 + h131
  have e39 : A 6 41 = 0 := by linear_combination h180 + A 6 41 * htwo
  have e40 : A 7 7 = A 0 0 := by linear_combination h12 + h60 + h119 + h174 - A 9 9 * htwo + A 11 11 * htwo
  have e41 : A 7 9 = 0 := by linear_combination h10
  have e42 : A 7 46 = 0 := by linear_combination h11
  have e43 : A 7 48 = 0 := by linear_combination h65 + h67 + h73 + h126 + h146 + h175 + h202 + h207 + h219 + h224 + A 0 44 * htwo + A 37 24 * htwo + A 1 44 * htwo
  have e44 : A 8 6 = 0 := by linear_combination h16 + A 8 6 * htwo
  have e45 : A 8 8 = A 0 0 := by linear_combination h12 + h17 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h177 + h201 + h208 + h220 + h225 + A 8 8 * htwo - A 9 9 * htwo - A 10 10 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e46 : A 8 39 = 0 := by linear_combination h18 + A 8 39 * htwo
  have e47 : A 8 41 = 0 := by linear_combination h19 + h50 + h108 + h131 + h179 + A 8 41 * htwo - A 10 42 * htwo
  have e48 : A 9 7 = 0 := by linear_combination h63 + h118 + h125 + h168 + h170 + h173 + A 29 33 * htwo
  have e49 : A 9 9 = A 0 0 := by linear_combination h60 + h119
  have e50 : A 9 46 = 0 := by linear_combination h15 + h65 + h67 + h73 + h126 + h146 + h202 + h207 + h219 + h224 + A 0 44 * htwo + A 37 24 * htwo + A 1 44 * htwo
  have e51 : A 9 48 = 0 := by linear_combination h176
  have e52 : A 10 10 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h177 + h201 + h208 + h220 + h225 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e53 : A 10 29 = 0 := by linear_combination h95 + A 10 29 * htwo
  have e54 : A 10 33 = 0 := by linear_combination h96 + A 10 33 * htwo
  have e55 : A 10 42 = 0 := by linear_combination h50 + h108 + h131 + h179
  have e56 : A 11 11 = A 0 0 := by linear_combination h12 + h60 + h119 + A 11 11 * htwo - A 9 9 * htwo
  have e57 : A 11 30 = 0 := by linear_combination h13 + A 11 30 * htwo
  have e58 : A 11 34 = 0 := by linear_combination h14 + A 11 34 * htwo
  have e59 : A 11 45 = 0 := by linear_combination h65 + h67 + h73 + h126 + h146 + h202 + h207 + h219 + h224 + A 0 44 * htwo + A 37 24 * htwo + A 1 44 * htwo
  have e60 : A 12 12 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h138 + h147 + h189 + h201 + h208 + h220 + h228 + A 12 12 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e61 : A 12 16 = 0 := by linear_combination h190 + A 12 16 * htwo
  have e62 : A 13 13 = A 0 0 := by linear_combination h12 + h24 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h143 + h147 + h181 + h201 + h208 + h220 + h229 - A 9 9 * htwo + A 21 21 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 39 39 * htwo
  have e63 : A 13 17 = 0 := by linear_combination h20
  have e64 : A 13 28 = 0 := by linear_combination h21
  have e65 : A 13 32 = 0 := by linear_combination h25 + h182 + h230 + A 21 24 * htwo
  have e66 : A 13 38 = 0 := by linear_combination h22
  have e67 : A 13 40 = 0 := by linear_combination h130 + h183
  have e68 : A 14 14 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h101 + h119 + h123 + h147 + h158 + h163 + h177 + h191 + h201 + h208 + h212 + h220 + h223 + h225 + h231 + A 14 14 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo - A 5 5 * htwo + A 1 3 * htwo
  have e69 : A 14 18 = 0 := by linear_combination h192 + A 14 18 * htwo
  have e70 : A 14 31 = 0 := by linear_combination h193 + A 14 31 * htwo
  have e71 : A 14 35 = 0 := by linear_combination h102 + h194 + A 14 35 * htwo
  have e72 : A 14 47 = 0 := by linear_combination h127
  have e73 : A 14 49 = 0 := by linear_combination h128
  have e74 : A 15 15 = A 15 15 := rfl
  have e75 : A 15 19 = 0 := by linear_combination h23
  have e76 : A 16 12 = 0 := by linear_combination h28 + A 16 12 * htwo
  have e77 : A 16 16 = A 0 0 := by linear_combination h12 + h29 + h60 + h62 + h75 + h98 + h119 + h123 + h138 + h147 + h201 + h208 + h220 + h228 + A 16 16 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e78 : A 17 13 = 0 := by linear_combination h185
  have e79 : A 17 17 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h143 + h147 + h201 + h208 + h220 + h229 + A 17 17 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 39 39 * htwo
  have e80 : A 17 28 = 0 := by linear_combination h230 + A 17 28 * htwo
  have e81 : A 17 32 = 0 := by linear_combination h186
  have e82 : A 17 38 = 0 := by linear_combination h26 + h130
  have e83 : A 17 40 = 0 := by linear_combination h187
  have e84 : A 18 14 = 0 := by linear_combination h30 + A 18 14 * htwo
  have e85 : A 18 18 = A 0 0 := by linear_combination h12 + h31 + h60 + h62 + h68 + h75 + h91 + h98 + h101 + h119 + h123 + h147 + h158 + h163 + h177 + h201 + h208 + h212 + h220 + h223 + h225 + h231 + A 18 18 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo - A 5 5 * htwo + A 1 3 * htwo
  have e86 : A 18 31 = 0 := by linear_combination h32 + h102 + A 18 31 * htwo
  have e87 : A 18 35 = 0 := by linear_combination h33 + A 18 35 * htwo
  have e88 : A 18 47 = 0 := by linear_combination h34 + A 18 47 * htwo
  have e89 : A 18 49 = 0 := by linear_combination h129
  have e90 : A 19 15 = 0 := by linear_combination h188
  have e91 : A 19 19 = A 15 15 := by linear_combination h27 + h184 - A 15 15 * htwo + A 23 23 * htwo
  have e92 : A 20 20 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h138 + h147 + h201 + h208 + h220 + h228 + A 20 20 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e93 : A 21 21 = A 0 0 := by linear_combination h12 + h24 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h143 + h147 + h201 + h208 + h220 + h229 + A 21 21 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 39 39 * htwo
  have e94 : A 21 24 = 0 := by linear_combination h25 + h230 + A 21 24 * htwo
  have e95 : A 21 37 = 0 := by linear_combination h130
  have e96 : A 22 22 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h101 + h119 + h123 + h147 + h158 + h163 + h177 + h201 + h208 + h212 + h220 + h223 + h225 + h231 + A 22 22 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo - A 5 5 * htwo + A 1 3 * htwo
  have e97 : A 22 27 = 0 := by linear_combination h102 + A 22 27 * htwo
  have e98 : A 22 50 = 0 := by linear_combination h35 + h129
  have e99 : A 23 23 = A 15 15 := by linear_combination h184 + A 23 23 * htwo - A 15 15 * htwo
  have e100 : A 24 21 = 0 := by linear_combination h48 + h105 + A 24 21 * htwo
  have e101 : A 24 24 = A 0 0 := by linear_combination h12 + h49 + h60 + h62 + h68 + h75 + h98 + h106 + h119 + h123 + h147 + h201 + h208 + h220 + h225 + A 24 24 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo - A 6 6 * htwo + A 1 3 * htwo
  have e102 : A 24 37 = 0 := by linear_combination h131
  have e103 : A 25 0 = 0 := by linear_combination h38 + h125 + h170 + h173 + h195 - A 25 1 * htwo + A 29 33 * htwo
  have e104 : A 25 1 = 0 := by linear_combination h38 + h125 + h170 + h173 + A 29 33 * htwo
  have e105 : A 25 2 = 0 := by linear_combination h132
  have e106 : A 25 3 = 0 := by linear_combination h203 + A 25 3 * htwo
  have e107 : A 25 25 = A 0 0 := by linear_combination h1 + h37 + h167 - A 0 0 * htwo - A 0 1 * htwo + A 29 29 * htwo
  have e108 : A 25 26 = 0 := by linear_combination h196
  have e109 : A 25 43 = 0 := by linear_combination h133
  have e110 : A 25 44 = 0 := by linear_combination h204 + A 25 44 * htwo
  have e111 : A 26 0 = 0 := by linear_combination h10 + h51 + h112 + A 26 0 * htwo - A 7 9 * htwo
  have e112 : A 26 1 = 0 := by linear_combination h41
  have e113 : A 26 2 = 0 := by linear_combination h52 + A 26 2 * htwo
  have e114 : A 26 3 = 0 := by linear_combination h53 + A 26 3 * htwo
  have e115 : A 26 25 = 0 := by linear_combination h40
  have e116 : A 26 26 = A 0 0 := by linear_combination h12 + h54 + h60 + h111 + h119 + h174 + A 26 26 * htwo - A 9 9 * htwo + A 11 11 * htwo - A 7 7 * htwo
  have e117 : A 26 43 = 0 := by linear_combination h55 + A 26 43 * htwo
  have e118 : A 26 44 = 0 := by linear_combination h56 + A 26 44 * htwo
  have e119 : A 27 22 = 0 := by linear_combination h232 + A 27 22 * htwo
  have e120 : A 27 27 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h166 + h177 + h201 + h208 + h212 + h220 + h225 + h231 + h233 + A 27 27 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 51 51 * htwo
  have e121 : A 27 50 = 0 := by linear_combination h47 + h134
  have e122 : A 28 13 = 0 := by linear_combination h104 + A 28 13 * htwo
  have e123 : A 28 17 = 0 := by linear_combination h105 + A 28 17 * htwo
  have e124 : A 28 28 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h106 + h119 + h123 + h147 + h201 + h208 + h220 + h225 + A 28 28 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo - A 6 6 * htwo + A 1 3 * htwo
  have e125 : A 28 32 = 0 := by linear_combination h107 + h178 + A 28 32 * htwo
  have e126 : A 28 38 = 0 := by linear_combination h50 + h131
  have e127 : A 28 40 = 0 := by linear_combination h109 + h180 + A 28 40 * htwo
  have e128 : A 29 10 = 0 := by linear_combination h36 + A 29 10 * htwo
  have e129 : A 29 29 = A 0 0 := by linear_combination h1 + h167 + A 29 29 * htwo - A 0 0 * htwo - A 0 1 * htwo
  have e130 : A 29 33 = 0 := by linear_combination h125 + h170 + h173 + A 29 33 * htwo
  have e131 : A 29 42 = 0 := by linear_combination h39 + A 29 42 * htwo
  have e132 : A 30 11 = 0 := by linear_combination h110 + A 30 11 * htwo
  have e133 : A 30 30 = A 0 0 := by linear_combination h12 + h60 + h111 + h119 + h174 + A 30 30 * htwo - A 9 9 * htwo + A 11 11 * htwo - A 7 7 * htwo
  have e134 : A 30 34 = 0 := by linear_combination h10 + h112 + A 30 34 * htwo - A 7 9 * htwo
  have e135 : A 30 45 = 0 := by linear_combination h113 + A 30 45 * htwo
  have e136 : A 31 14 = 0 := by linear_combination h42 + A 31 14 * htwo
  have e137 : A 31 18 = 0 := by linear_combination h43 + h232 + A 31 18 * htwo
  have e138 : A 31 31 = A 0 0 := by linear_combination h12 + h44 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h166 + h177 + h201 + h208 + h212 + h220 + h225 + h231 + h233 + A 31 31 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 51 51 * htwo
  have e139 : A 31 35 = 0 := by linear_combination h45 + A 31 35 * htwo
  have e140 : A 31 47 = 0 := by linear_combination h46 + A 31 47 * htwo
  have e141 : A 31 49 = 0 := by linear_combination h134
  have e142 : A 32 13 = 0 := by linear_combination h114 + A 32 13 * htwo
  have e143 : A 32 17 = 0 := by linear_combination h57
  have e144 : A 32 28 = 0 := by linear_combination h58
  have e145 : A 32 32 = A 0 0 := by linear_combination h12 + h17 + h60 + h62 + h68 + h75 + h98 + h115 + h119 + h123 + h147 + h177 + h201 + h208 + h220 + h225 + A 32 32 * htwo - A 9 9 * htwo - A 10 10 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e146 : A 32 38 = 0 := by linear_combination h59
  have e147 : A 32 40 = 0 := by linear_combination h19 + h50 + h108 + h116 + h131 + h179 + A 32 40 * htwo - A 10 42 * htwo
  have e148 : A 33 10 = 0 := by linear_combination h2 + A 33 10 * htwo
  have e149 : A 33 29 = 0 := by linear_combination h3 + h8 + h124 + A 33 29 * htwo
  have e150 : A 33 33 = A 0 0 := by linear_combination h4 + h9 + h12 + h60 + h119 + h122 + A 33 33 * htwo - A 9 9 * htwo
  have e151 : A 33 42 = 0 := by linear_combination h5 + A 33 42 * htwo
  have e152 : A 34 11 = 0 := by linear_combination h117 + A 34 11 * htwo
  have e153 : A 34 30 = 0 := by linear_combination h63 + h125 + h168 + h170 + h173 + A 29 33 * htwo
  have e154 : A 34 34 = A 0 0 := by linear_combination h60
  have e155 : A 34 45 = 0 := by linear_combination h120 + A 34 45 * htwo
  have e156 : A 35 14 = 0 := by linear_combination h197 + h232 + A 35 14 * htwo
  have e157 : A 35 18 = 0 := by linear_combination h198 + A 35 18 * htwo
  have e158 : A 35 31 = 0 := by linear_combination h199 + A 35 31 * htwo
  have e159 : A 35 35 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h166 + h177 + h200 + h201 + h208 + h212 + h220 + h225 + h231 + h233 + A 35 35 * htwo - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo - A 51 51 * htwo
  have e160 : A 35 47 = 0 := by linear_combination h135
  have e161 : A 35 49 = 0 := by linear_combination h136
  have e162 : A 36 4 = 0 := by linear_combination h137
  have e163 : A 36 36 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h138 + h147 + h201 + h208 + h220 + A 36 36 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e164 : A 37 21 = 0 := by linear_combination h66 + h140 + A 37 21 * htwo
  have e165 : A 37 24 = 0 := by linear_combination h67 + h224 + A 37 24 * htwo
  have e166 : A 37 37 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h147 + h201 + h208 + h220 + A 37 37 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e167 : A 38 13 = 0 := by linear_combination h139 + A 38 13 * htwo
  have e168 : A 38 17 = 0 := by linear_combination h140 + A 38 17 * htwo
  have e169 : A 38 28 = 0 := by linear_combination h224 + A 38 28 * htwo
  have e170 : A 38 32 = 0 := by linear_combination h205
  have e171 : A 38 38 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h201 + h208 + h220 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e172 : A 38 40 = 0 := by linear_combination h206
  have e173 : A 39 6 = 0 := by linear_combination h141 + h224 + A 38 28 * htwo
  have e174 : A 39 8 = 0 := by linear_combination h142 + h205
  have e175 : A 39 39 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h143 + h147 + h201 + h208 + h220 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e176 : A 39 41 = 0 := by linear_combination h144 + h206
  have e177 : A 40 13 = 0 := by linear_combination h145 + A 40 13 * htwo
  have e178 : A 40 17 = 0 := by linear_combination h69
  have e179 : A 40 28 = 0 := by linear_combination h70
  have e180 : A 40 32 = 0 := by linear_combination h67 + h207 + h224 + A 37 24 * htwo
  have e181 : A 40 38 = 0 := by linear_combination h71
  have e182 : A 40 40 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h147 + h201 + h220 + A 40 40 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e183 : A 41 6 = 0 := by linear_combination h72 + A 41 6 * htwo
  have e184 : A 41 8 = 0 := by linear_combination h67 + h146 + h207 + h224 + A 37 24 * htwo
  have e185 : A 41 39 = 0 := by linear_combination h74 + A 41 39 * htwo
  have e186 : A 41 41 = A 0 0 := by linear_combination h12 + h60 + h62 + h75 + h98 + h119 + h123 + h201 + h220 + A 41 41 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e187 : A 42 10 = 0 := by linear_combination h67 + h73 + h146 + h207 + h224 + A 37 24 * htwo
  have e188 : A 42 29 = 0 := by linear_combination h149 + A 42 29 * htwo
  have e189 : A 42 33 = 0 := by linear_combination h150 + A 42 33 * htwo
  have e190 : A 42 42 = A 0 0 := by linear_combination h12 + h60 + h62 + h98 + h119 + h123 + h201 + h220 + A 42 42 * htwo - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e191 : A 43 0 = 0 := by linear_combination h77 + h209 - A 43 1 * htwo
  have e192 : A 43 1 = 0 := by linear_combination h77
  have e193 : A 43 2 = 0 := by linear_combination h67 + h73 + h146 + h148 + h207 + h224 + A 37 24 * htwo
  have e194 : A 43 3 = 0 := by linear_combination h65 + h67 + h73 + h126 + h146 + h202 + h207 + h219 + h224 + h226 + A 43 3 * htwo + A 0 44 * htwo + A 37 24 * htwo - A 11 45 * htwo + A 1 44 * htwo
  have e195 : A 43 25 = 0 := by linear_combination h76
  have e196 : A 43 26 = 0 := by linear_combination h210
  have e197 : A 43 43 = A 0 0 := by linear_combination h12 + h60 + h62 + h98 + h119 + h123 + h151 + h201 + h220 - A 9 9 * htwo + A 0 3 * htwo - A 3 2 * htwo + A 1 3 * htwo + A 42 42 * htwo
  have e198 : A 43 44 = 0 := by linear_combination h227 + A 43 44 * htwo
  have e199 : A 44 0 = 0 := by linear_combination h154 + A 44 0 * htwo
  have e200 : A 44 1 = 0 := by linear_combination h79
  have e201 : A 44 2 = 0 := by linear_combination h152
  have e202 : A 44 3 = 0 := by linear_combination h79 + h155 + h156 + A 44 3 * htwo - A 45 11 * htwo
  have e203 : A 44 25 = 0 := by linear_combination h78
  have e204 : A 44 26 = 0 := by linear_combination h157 + A 44 26 * htwo
  have e205 : A 44 43 = 0 := by linear_combination h153
  have e206 : A 44 44 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h177 + h201 + h208 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e207 : A 45 11 = 0 := by linear_combination h79 + h155
  have e208 : A 45 30 = 0 := by linear_combination h81
  have e209 : A 45 34 = 0 := by linear_combination h80
  have e210 : A 45 45 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h158 + h177 + h201 + h208 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e211 : A 46 7 = 0 := by linear_combination h159
  have e212 : A 46 9 = 0 := by linear_combination h79 + h82 + h155
  have e213 : A 46 46 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h83 + h98 + h119 + h123 + h147 + h158 + h177 + h201 + h208 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e214 : A 46 48 = 0 := by linear_combination h211
  have e215 : A 47 14 = 0 := by linear_combination h213 + h222 + A 47 14 * htwo
  have e216 : A 47 18 = 0 := by linear_combination h214 + A 47 18 * htwo
  have e217 : A 47 31 = 0 := by linear_combination h215 + A 47 31 * htwo
  have e218 : A 47 35 = 0 := by linear_combination h165 + h216 + A 47 35 * htwo
  have e219 : A 47 47 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h83 + h98 + h119 + h123 + h147 + h158 + h160 + h177 + h201 + h208 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e220 : A 47 49 = 0 := by linear_combination h161 + h211
  have e221 : A 48 7 = 0 := by linear_combination h162
  have e222 : A 48 9 = 0 := by linear_combination h84
  have e223 : A 48 46 = 0 := by linear_combination h85
  have e224 : A 48 48 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h158 + h177 + h201 + h208 + h212 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e225 : A 49 14 = 0 := by linear_combination h86 + A 49 14 * htwo
  have e226 : A 49 18 = 0 := by linear_combination h87 + h222 + A 49 18 * htwo
  have e227 : A 49 31 = 0 := by linear_combination h88 + h165 + A 49 31 * htwo
  have e228 : A 49 35 = 0 := by linear_combination h89 + A 49 35 * htwo
  have e229 : A 49 47 = 0 := by linear_combination h90 + A 49 47 * htwo
  have e230 : A 49 49 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h98 + h119 + h123 + h147 + h158 + h163 + h177 + h201 + h208 + h212 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e231 : A 50 22 = 0 := by linear_combination h222 + A 50 22 * htwo
  have e232 : A 50 27 = 0 := by linear_combination h165 + A 50 27 * htwo
  have e233 : A 50 50 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h177 + h201 + h208 + h212 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have e234 : A 51 5 = 0 := by linear_combination h164 + h222 + A 50 22 * htwo
  have e235 : A 51 51 = A 0 0 := by linear_combination h12 + h60 + h62 + h68 + h75 + h91 + h98 + h119 + h123 + h147 + h158 + h163 + h166 + h177 + h201 + h208 + h212 + h220 + h225 + h231 - A 9 9 * htwo + A 0 3 * htwo + A 37 37 * htwo - A 3 2 * htwo + A 1 3 * htwo
  have he : ∀ p ∈ positions,
      A p.1 p.2 = diagonalShape (A 0 0) (A 15 15) p.1 p.2 := by
    simp only [positions, List.forall_mem_cons, List.forall_mem_nil, and_true,
      diagonalShape, Matrix.diagonal_apply, exceptional]
    norm_num only [Bool.or_eq_true, beq_iff_eq, Fin.reduceEq, or_false, false_or,
      Bool.false_eq_true, if_true, if_false]
    exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69, e70, e71, e72, e73, e74, e75, e76, e77, e78, e79, e80, e81, e82, e83, e84, e85, e86, e87, e88, e89, e90, e91, e92, e93, e94, e95, e96, e97, e98, e99, e100, e101, e102, e103, e104, e105, e106, e107, e108, e109, e110, e111, e112, e113, e114, e115, e116, e117, e118, e119, e120, e121, e122, e123, e124, e125, e126, e127, e128, e129, e130, e131, e132, e133, e134, e135, e136, e137, e138, e139, e140, e141, e142, e143, e144, e145, e146, e147, e148, e149, e150, e151, e152, e153, e154, e155, e156, e157, e158, e159, e160, e161, e162, e163, e164, e165, e166, e167, e168, e169, e170, e171, e172, e173, e174, e175, e176, e177, e178, e179, e180, e181, e182, e183, e184, e185, e186, e187, e188, e189, e190, e191, e192, e193, e194, e195, e196, e197, e198, e199, e200, e201, e202, e203, e204, e205, e206, e207, e208, e209, e210, e211, e212, e213, e214, e215, e216, e217, e218, e219, e220, e221, e222, e223, e224, e225, e226, e227, e228, e229, e230, e231, e232, e233, e234, e235, by simp⟩
  ext i j
  by_cases hij : degree i = degree j
  · exact he (i, j) (positions_complete i j hij)
  · rw [hd i j hij]
    exact (Matrix.diagonal_apply_ne _ (fun h => hij (congrArg degree h))).symm

end ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
