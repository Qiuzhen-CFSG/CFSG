module
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer.FiniteCalculation
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer.MiddleOperators
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.DividedPowers
/-!
# Comparing the four test matrices with actual root operators

The simple-root cases use certified integral columns. For 1100 and 0011,
the characteristic-two route-comparison theorem permits the one-reflection
routes from the adjacent middle simple roots. Sparse integer multiplication
certifies these two conjugations, including their Cartan columns. Column
reconstruction and reduction modulo two turn the final comparisons into
permutations of the odd-entry supports; all numerical checks use kernel reduction.
Source: Geck's integral operators and GLS3 §1.12, §2.6.
-/
@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.Cartan.FieldSeparation.TraceValues
open scoped Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency true

private lemma matrix_neg_entries (a : Sparse) :
    matrix (a.map fun e => (e.1, e.2.1, -e.2.2)) = -matrix a := by
  induction a with
  | nil => simp
  | cons e a ih =>
    simp only [List.map_cons, matrix_cons, ih, ← Matrix.single_neg]
    abel1

private lemma reindex_specialize' {F : Type*} [CommRing F] (A : Matrix Basis Basis ℤ) :
    reindex (specializeMatrix (S := F) A) = (reindex A).map (Int.castRingHom F) := rfl

private lemma reindex_smul' (t : ℤ) (A : Matrix Basis Basis ℤ) :
    reindex (t • A) = t • reindex A := rfl

private lemma matrix_cons_units (e : Entry) (a : Sparse) :
    matrix (e :: a) = e.2.2 • Matrix.single e.1 e.2.1 (1 : ℤ) + matrix a := by
  simp [matrix_cons, smul_eq_mul]

private lemma cast_matrix_cons {F : Type*} [CommRing F] (e : Entry) (a : Sparse) :
    (matrix (e :: a)).map (Int.castRingHom F) =
      (e.2.2 : F) • Matrix.single e.1 e.2.1 (1 : F) +
        (matrix a).map (Int.castRingHom F) := by
  ext i j
  simp only [matrix_cons, Matrix.map_apply, Matrix.add_apply, Int.coe_castRingHom,
    Int.cast_add, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  split_ifs <;> simp

private lemma matrix_filter_zero (a : Sparse) :
    matrix (a.filter fun e => e.2.2 != 0) = matrix a := by
  induction a with
  | nil => rfl
  | cons e a ih =>
    by_cases h : e.2.2 = 0
    · simp [List.filter_cons, h, matrix_cons, ih]
    · simp [List.filter_cons, h, matrix_cons, ih]

private lemma column_matrix (c : Fin 52 → Fin 52 × ℤ) :
    (fun i j => if i = (c j).1 then (c j).2 else 0) =
      matrix ((List.finRange 52).map fun j => ((c j).1, j, (c j).2)) := by
  rw [matrix, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  ext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single j]
  · simp [Matrix.single_apply, eq_comm]
  · intro b _ hb
    simp [Matrix.single_apply, hb]
  · simp

private def oddSupport (a : Sparse) : List (Fin 52 × Fin 52) :=
  a.filterMap fun e => if e.2.2 % 2 = 1 then some (e.1, e.2.1) else none

private lemma cast_matrix_support {F : Type*} [CommRing F] [CharP F 2] (a : Sparse) :
    (matrix a).map (Int.castRingHom F) =
      ((oddSupport a).map fun p => Matrix.single p.1 p.2 (1 : F)).sum := by
  induction a with
  | nil => simp [oddSupport]
  | cons e a ih =>
    rw [cast_matrix_cons, CharTwo.intCast_eq_mod]
    have hz : e.2.2 % 2 = 0 ∨ e.2.2 % 2 = 1 := by omega
    rcases hz with hz | hz <;> simp [oddSupport, hz] <;> exact ih

private lemma cast_eq_test_of_support {F : Type*} [CommRing F] [CharP F 2]
    (a : Sparse) (k : Fin 4) (h : (oddSupport a).Perm (operatorSupport k)) :
    (matrix a).map (Int.castRingHom F) = testOperator k := by
  rw [cast_matrix_support]
  exact (h.map fun p => Matrix.single p.1 p.2 (1 : F)).sum_eq

private def middleEntries1 : Sparse := [(34, 0, 1), (34, 1, 2), (34, 2, 2), (10, 8, 1), (9, 11, 1), (20, 16, 1), (22, 18, 1), (17, 21, 1), (19, 23, 1), (28, 24, 1), (30, 26, 1), (25, 29, 1), (27, 31, 1), (1, 33, 1), (38, 37, 1), (42, 41, 1), (46, 45, 1), (50, 49, 1)]

private lemma middleTable1_sparse : middleTable1 = matrix middleEntries1 := by
  change (fun i j => if i = (middleColumns1 j).1 then (middleColumns1 j).2 else 0) = _
  rw [column_matrix, ← matrix_filter_zero]
  congr 1

private lemma middle1_cast {F : Type*} [CommRing F] [CharP F 2] :
    middleTable1.map (Int.castRingHom F) = testOperator 0 := by
  rw [middleTable1_sparse]
  apply cast_eq_test_of_support
  decide +kernel

private def middleEntries2 : Sparse := [(11, 1, 1), (11, 2, 2), (11, 3, 1), (21, 4, 2), (23, 5, 2), (29, 6, 2), (31, 7, 2), (33, 8, 2), (35, 9, 2), (2, 10, 1), (4, 20, 1), (5, 22, 1), (6, 28, 1), (7, 30, 1), (8, 32, 1), (9, 34, 1), (37, 36, 1), (39, 38, 1), (41, 40, 1), (43, 42, 1), (45, 44, 1), (47, 46, 1), (49, 48, 1), (51, 50, 1)]

private lemma middleTable2_sparse : middleTable2 = matrix middleEntries2 := by
  change (fun i j => if i = (middleColumns2 j).1 then (middleColumns2 j).2 else 0) = _
  rw [column_matrix, ← matrix_filter_zero]
  congr 1

private lemma middle2_cast {F : Type*} [CommRing F] [CharP F 2] :
    middleTable2.map (Int.castRingHom F) = testOperator 1 := by
  rw [middleTable2_sparse]
  apply cast_eq_test_of_support
  decide +kernel

private def endTits0 : Sparse :=
  [(0, 0, -1), (0, 1, -1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 8, -1), (7, 9, 1), (8, 6, 1), (9, 7, -1), (10, 10, 1), (11, 11, 1), (12, 16, -1), (13, 17, 1), (14, 18, -1), (15, 19, 1), (16, 12, 1), (17, 13, -1), (18, 14, 1), (19, 15, -1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 26, 1), (26, 25, 1), (27, 27, 1), (28, 32, -1), (29, 33, -1), (30, 34, 1), (31, 35, 1), (32, 28, 1), (33, 29, 1), (34, 30, -1), (35, 31, -1), (36, 36, 1), (37, 37, 1), (38, 40, -1), (39, 41, -1), (40, 38, 1), (41, 39, 1), (42, 42, 1), (43, 43, 1), (44, 44, 1), (45, 45, 1), (46, 48, -1), (47, 49, -1), (48, 46, 1), (49, 47, 1), (50, 50, 1), (51, 51, 1)]

private lemma endTits0_check :
    matrix (sparseMul (sparseMul
      (identityEntries ++ positive0Linear ++ positive0Quadratic)
      (identityEntries ++ (negative0Linear.map fun e => (e.1, e.2.1, -e.2.2)) ++
        negative0Quadratic))
      (identityEntries ++ positive0Linear ++ positive0Quadratic)) = matrix endTits0 := by
  have hproduct : (sparseMul (sparseMul
      (identityEntries ++ positive0Linear ++ positive0Quadratic)
      (identityEntries ++ (negative0Linear.map fun e => (e.1, e.2.1, -e.2.2)) ++
        negative0Quadratic))
      (identityEntries ++ positive0Linear ++ positive0Quadratic)) = [(0, 0, 1), (0, 25, 1), (0, 26, -1), (0, 0, -2), (0, 1, -1), (0, 25, -1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (6, 8, -1), (6, 6, -1), (7, 7, 1), (7, 9, 1), (8, 8, 1), (8, 6, 1), (9, 9, 1), (9, 7, -1), (9, 9, -1), (10, 10, 1), (11, 11, 1), (12, 12, 1), (12, 16, -1), (12, 12, -1), (13, 13, 1), (13, 17, 1), (14, 14, 1), (14, 18, -1), (14, 14, -1), (15, 15, 1), (15, 19, 1), (16, 16, 1), (16, 12, 1), (17, 17, 1), (17, 13, -1), (17, 17, -1), (18, 18, 1), (18, 14, 1), (19, 19, 1), (19, 15, -1), (19, 19, -1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (25, 0, -2), (25, 25, -2), (25, 1, -1), (25, 26, 1), (25, 0, 2), (25, 1, 1), (25, 25, 1), (26, 26, 1), (26, 0, 2), (26, 1, 1), (26, 25, 1), (27, 27, 1), (28, 28, 1), (28, 32, -1), (28, 28, -1), (29, 29, 1), (29, 33, -1), (29, 29, -1), (30, 30, 1), (30, 34, 1), (31, 31, 1), (31, 35, 1), (32, 32, 1), (32, 28, 1), (33, 33, 1), (33, 29, 1), (34, 34, 1), (34, 30, -1), (34, 34, -1), (35, 35, 1), (35, 31, -1), (35, 35, -1), (36, 36, 1), (37, 37, 1), (38, 38, 1), (38, 40, -1), (38, 38, -1), (39, 39, 1), (39, 41, -1), (39, 39, -1), (40, 40, 1), (40, 38, 1), (41, 41, 1), (41, 39, 1), (42, 42, 1), (43, 43, 1), (44, 44, 1), (45, 45, 1), (46, 46, 1), (46, 48, -1), (46, 46, -1), (47, 47, 1), (47, 49, -1), (47, 47, -1), (48, 48, 1), (48, 46, 1), (49, 49, 1), (49, 47, 1), (50, 50, 1), (51, 51, 1), (0, 25, 1), (0, 0, -2), (0, 25, -2), (0, 1, -1), (0, 26, 1), (0, 0, 2), (0, 1, 1), (0, 25, 1), (7, 9, 1), (7, 7, -1), (7, 9, -1), (8, 6, 1), (8, 8, -1), (8, 6, -1), (13, 17, 1), (13, 13, -1), (13, 17, -1), (15, 19, 1), (15, 15, -1), (15, 19, -1), (16, 12, 1), (16, 16, -1), (16, 12, -1), (18, 14, 1), (18, 18, -1), (18, 14, -1), (26, 0, 2), (26, 25, 2), (26, 26, -2), (26, 0, -4), (26, 1, -2), (26, 25, -2), (26, 1, 1), (30, 34, 1), (30, 30, -1), (30, 34, -1), (31, 35, 1), (31, 31, -1), (31, 35, -1), (32, 28, 1), (32, 32, -1), (32, 28, -1), (33, 29, 1), (33, 33, -1), (33, 29, -1), (40, 38, 1), (40, 40, -1), (40, 38, -1), (41, 39, 1), (41, 41, -1), (41, 39, -1), (48, 46, 1), (48, 48, -1), (48, 46, -1), (49, 47, 1), (49, 49, -1), (49, 47, -1), (26, 25, 1), (26, 0, -2), (26, 25, -2), (26, 1, -1), (26, 26, 1), (26, 0, 2), (26, 1, 1), (26, 25, 1)] := by
    decide +kernel
  rw [hproduct]
  simp only [endTits0, matrix_cons_units, matrix_nil]
  abel

private lemma reindex_tits0 :
    reindex (titsLift (typeF4RootPairing_baseEquiv 0)) = matrix endTits0 := by
  rw [← endTits0_check, matrix_mul, matrix_mul]
  simp only [titsLift, eUnipotent, fUnipotent, map_mul, map_add, map_one, map_neg, reindex_smul',
    eDividedPower_one, fDividedPower_one, eMatrix_0, fMatrix_0,
    eDividedPower_0_two, fDividedPower_0_two,
    eDividedPower_0_three, fDividedPower_0_three,
    one_pow, one_smul, neg_one_smul, smul_zero, add_zero, neg_one_sq,
    matrix_append, matrix_identity]
  rw [matrix_neg_entries]


private lemma conjugate0_cast {F : Type*} [CommRing F] [CharP F 2] :
    (matrix (sparseMul (sparseMul endTits0 middleEntries1) endTits0)).map
      (Int.castRingHom F) = testOperator 2 := by
  have hproduct : sparseMul (sparseMul endTits0 middleEntries1) endTits0 = [(0, 29, -1), (1, 29, 1), (7, 11, 1), (10, 6, 1), (13, 21, 1), (15, 23, 1), (20, 12, 1), (22, 14, 1), (26, 33, -1), (27, 35, 1), (30, 0, -1), (30, 1, -1), (30, 1, 2), (30, 2, 2), (32, 24, 1), (34, 25, -1), (40, 37, 1), (42, 39, 1), (48, 45, 1), (50, 47, 1)] := by
    decide +kernel
  rw [hproduct]
  apply cast_eq_test_of_support
  decide +kernel

private def endTits3 : Sparse :=
  [(0, 0, 1), (1, 1, 1), (2, 2, 1), (3, 2, -1), (3, 3, -1), (4, 36, -1), (5, 51, 1), (6, 39, 1), (7, 48, -1), (8, 41, 1), (9, 46, -1), (10, 42, 1), (11, 45, -1), (12, 12, 1), (13, 32, 1), (14, 35, 1), (15, 15, 1), (16, 16, 1), (17, 28, 1), (18, 31, 1), (19, 19, 1), (20, 20, 1), (21, 24, 1), (22, 27, 1), (23, 23, 1), (24, 21, 1), (25, 25, 1), (26, 26, 1), (27, 22, 1), (28, 17, 1), (29, 29, 1), (30, 30, 1), (31, 18, 1), (32, 13, 1), (33, 33, 1), (34, 34, 1), (35, 14, 1), (36, 4, 1), (37, 37, -1), (38, 38, -1), (39, 6, -1), (40, 40, -1), (41, 8, -1), (42, 10, -1), (43, 44, 1), (44, 43, 1), (45, 11, 1), (46, 9, 1), (47, 47, -1), (48, 7, 1), (49, 49, -1), (50, 50, -1), (51, 5, -1)]

private lemma endTits3_check :
    matrix (sparseMul (sparseMul
      (identityEntries ++ positive3Linear ++ positive3Quadratic)
      (identityEntries ++ (negative3Linear.map fun e => (e.1, e.2.1, -e.2.2)) ++
        negative3Quadratic))
      (identityEntries ++ positive3Linear ++ positive3Quadratic)) = matrix endTits3 := by
  have hproduct : (sparseMul (sparseMul
      (identityEntries ++ positive3Linear ++ positive3Quadratic)
      (identityEntries ++ (negative3Linear.map fun e => (e.1, e.2.1, -e.2.2)) ++
        negative3Quadratic))
      (identityEntries ++ positive3Linear ++ positive3Quadratic)) = [(0, 0, 1), (1, 1, 1), (2, 2, 1), (3, 3, 1), (3, 43, 1), (3, 44, -1), (3, 2, -1), (3, 3, -2), (3, 43, -1), (4, 4, 1), (4, 36, -1), (4, 4, -1), (5, 5, 1), (5, 51, 1), (6, 6, 1), (6, 39, 1), (7, 7, 1), (7, 48, -1), (7, 7, -1), (8, 8, 1), (8, 41, 1), (9, 9, 1), (9, 46, -1), (9, 9, -1), (10, 10, 1), (10, 42, 1), (11, 11, 1), (11, 45, -1), (11, 11, -1), (12, 12, 1), (13, 13, 1), (13, 40, -2), (13, 13, -2), (13, 32, 1), (13, 40, 2), (13, 13, 1), (14, 14, 1), (14, 47, 2), (14, 35, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (17, 38, -2), (17, 17, -2), (17, 28, 1), (17, 38, 2), (17, 17, 1), (18, 18, 1), (18, 49, 2), (18, 31, 1), (19, 19, 1), (20, 20, 1), (21, 21, 1), (21, 37, -2), (21, 21, -2), (21, 24, 1), (21, 37, 2), (21, 21, 1), (22, 22, 1), (22, 50, 2), (22, 27, 1), (23, 23, 1), (24, 24, 1), (24, 37, 2), (24, 21, 1), (25, 25, 1), (26, 26, 1), (27, 27, 1), (27, 50, -2), (27, 27, -2), (27, 22, 1), (27, 50, 2), (27, 27, 1), (28, 28, 1), (28, 38, 2), (28, 17, 1), (29, 29, 1), (30, 30, 1), (31, 31, 1), (31, 49, -2), (31, 31, -2), (31, 18, 1), (31, 49, 2), (31, 31, 1), (32, 32, 1), (32, 40, 2), (32, 13, 1), (33, 33, 1), (34, 34, 1), (35, 35, 1), (35, 47, -2), (35, 35, -2), (35, 14, 1), (35, 47, 2), (35, 35, 1), (36, 36, 1), (36, 4, 1), (37, 37, 1), (37, 21, 1), (37, 24, -1), (37, 37, -2), (37, 21, -1), (38, 38, 1), (38, 17, 1), (38, 28, -1), (38, 38, -2), (38, 17, -1), (39, 39, 1), (39, 6, -1), (39, 39, -1), (40, 40, 1), (40, 13, 1), (40, 32, -1), (40, 40, -2), (40, 13, -1), (41, 41, 1), (41, 8, -1), (41, 41, -1), (42, 42, 1), (42, 10, -1), (42, 42, -1), (43, 43, 1), (43, 2, -1), (43, 3, -2), (43, 43, -2), (43, 44, 1), (43, 2, 1), (43, 3, 2), (43, 43, 1), (44, 44, 1), (44, 2, 1), (44, 3, 2), (44, 43, 1), (45, 45, 1), (45, 11, 1), (46, 46, 1), (46, 9, 1), (47, 47, 1), (47, 35, 1), (47, 14, -1), (47, 47, -2), (47, 35, -1), (48, 48, 1), (48, 7, 1), (49, 49, 1), (49, 31, 1), (49, 18, -1), (49, 49, -2), (49, 31, -1), (50, 50, 1), (50, 27, 1), (50, 22, -1), (50, 50, -2), (50, 27, -1), (51, 51, 1), (51, 5, -1), (51, 51, -1), (3, 43, 1), (3, 2, -1), (3, 3, -2), (3, 43, -2), (3, 44, 1), (3, 2, 1), (3, 3, 2), (3, 43, 1), (5, 51, 1), (5, 5, -1), (5, 51, -1), (6, 39, 1), (6, 6, -1), (6, 39, -1), (8, 41, 1), (8, 8, -1), (8, 41, -1), (10, 42, 1), (10, 10, -1), (10, 42, -1), (14, 47, 2), (14, 35, 2), (14, 14, -2), (14, 47, -4), (14, 35, -2), (18, 49, 2), (18, 31, 2), (18, 18, -2), (18, 49, -4), (18, 31, -2), (22, 50, 2), (22, 27, 2), (22, 22, -2), (22, 50, -4), (22, 27, -2), (24, 37, 2), (24, 21, 2), (24, 24, -2), (24, 37, -4), (24, 21, -2), (28, 38, 2), (28, 17, 2), (28, 28, -2), (28, 38, -4), (28, 17, -2), (32, 40, 2), (32, 13, 2), (32, 32, -2), (32, 40, -4), (32, 13, -2), (36, 4, 1), (36, 36, -1), (36, 4, -1), (37, 21, 1), (37, 37, -2), (37, 21, -2), (37, 24, 1), (37, 37, 2), (37, 21, 1), (38, 17, 1), (38, 38, -2), (38, 17, -2), (38, 28, 1), (38, 38, 2), (38, 17, 1), (40, 13, 1), (40, 40, -2), (40, 13, -2), (40, 32, 1), (40, 40, 2), (40, 13, 1), (44, 2, 1), (44, 3, 2), (44, 43, 2), (44, 44, -2), (44, 2, -2), (44, 3, -4), (44, 43, -2), (45, 11, 1), (45, 45, -1), (45, 11, -1), (46, 9, 1), (46, 46, -1), (46, 9, -1), (47, 35, 1), (47, 47, -2), (47, 35, -2), (47, 14, 1), (47, 47, 2), (47, 35, 1), (48, 7, 1), (48, 48, -1), (48, 7, -1), (49, 31, 1), (49, 49, -2), (49, 31, -2), (49, 18, 1), (49, 49, 2), (49, 31, 1), (50, 27, 1), (50, 50, -2), (50, 27, -2), (50, 22, 1), (50, 50, 2), (50, 27, 1), (14, 35, 1), (14, 47, -2), (14, 35, -2), (14, 14, 1), (14, 47, 2), (14, 35, 1), (18, 31, 1), (18, 49, -2), (18, 31, -2), (18, 18, 1), (18, 49, 2), (18, 31, 1), (22, 27, 1), (22, 50, -2), (22, 27, -2), (22, 22, 1), (22, 50, 2), (22, 27, 1), (24, 21, 1), (24, 37, -2), (24, 21, -2), (24, 24, 1), (24, 37, 2), (24, 21, 1), (28, 17, 1), (28, 38, -2), (28, 17, -2), (28, 28, 1), (28, 38, 2), (28, 17, 1), (32, 13, 1), (32, 40, -2), (32, 13, -2), (32, 32, 1), (32, 40, 2), (32, 13, 1), (44, 43, 1), (44, 2, -1), (44, 3, -2), (44, 43, -2), (44, 44, 1), (44, 2, 1), (44, 3, 2), (44, 43, 1)] := by
    decide +kernel
  rw [hproduct]
  simp only [endTits3, matrix_cons_units, matrix_nil]
  abel

private lemma reindex_tits3 :
    reindex (titsLift (typeF4RootPairing_baseEquiv 3)) = matrix endTits3 := by
  rw [← endTits3_check, matrix_mul, matrix_mul]
  simp only [titsLift, eUnipotent, fUnipotent, map_mul, map_add, map_one, map_neg, reindex_smul',
    eDividedPower_one, fDividedPower_one, eMatrix_3, fMatrix_3,
    eDividedPower_3_two, fDividedPower_3_two,
    eDividedPower_3_three, fDividedPower_3_three,
    one_pow, one_smul, neg_one_smul, smul_zero, add_zero, neg_one_sq,
    matrix_append, matrix_identity]
  rw [matrix_neg_entries]


private lemma conjugate3_cast {F : Type*} [CommRing F] [CharP F 2] :
    (matrix (sparseMul (sparseMul endTits3 middleEntries2) endTits3)).map
      (Int.castRingHom F) = testOperator 3 := by
  have hproduct : sparseMul (sparseMul endTits3 middleEntries2) endTits3 = [(2, 42, 1), (3, 42, -1), (5, 50, -1), (6, 38, -1), (8, 40, -1), (11, 43, -1), (14, 46, -2), (18, 48, -2), (23, 51, 2), (24, 36, -2), (29, 39, 2), (33, 41, 2), (36, 20, 1), (37, 4, -1), (39, 17, -1), (41, 13, -1), (44, 10, -1), (45, 1, 1), (45, 2, 2), (45, 2, -1), (45, 3, -1), (46, 34, 1), (47, 9, -1), (48, 30, 1), (49, 7, -1), (51, 27, -1)] := by
    decide +kernel
  rw [hproduct]
  apply cast_eq_test_of_support
  decide +kernel

private lemma testRoot_positive (k : Fin 4) : typeF4RootPairing_base.IsPos (testRoot k) := by
  have hp (i : Fin 4) := typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property
  fin_cases k
  · change typeF4RootPairing_base.IsPos (testRoot 0)
    have hr : testRoot 0 = (typeF4RootPairing_baseEquiv 1 : typeF4Roots) := by
      apply Subtype.ext
      ext q
      fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [hr]
    exact hp 1
  · change typeF4RootPairing_base.IsPos (testRoot 1)
    have hr : testRoot 1 = (typeF4RootPairing_baseEquiv 2 : typeF4Roots) := by
      apply Subtype.ext
      ext q
      fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [hr]
    exact hp 2
  · apply (hp 0).add (hp 1)
    ext q
    fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
  · apply (hp 3).add (hp 2)
    ext q
    fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]

private lemma tits_inv_cast {F : Type*} [CommRing F] [CharP F 2]
    (i : typeF4RootPairing_base.support) :
    specializeMatrix (S := F) (titsLiftInv i) = specializeMatrix (titsLift i) := by
  simp only [titsLiftInv, titsLift, specializeMatrix, Matrix.map_mul,
    ReeF4.WordRelations.Faithfulness.Adjoint.map_eUnipotent,
    ReeF4.WordRelations.Faithfulness.Adjoint.map_fUnipotent,
    Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

/-- The finite test matrices are precisely the four actual degree-one operators. -/
theorem rootOperator_testRoot (m : ℕ) (k : Fin 4) :
    reindex (rootOperator m (testRoot k)) = testOperator k := by
  fin_cases k
  · change reindex (rootOperator m (testRoot 0)) = testOperator 0
    have hr : testRoot 0 = (typeF4RootPairing_baseEquiv 1 : typeF4Roots) := by
      apply Subtype.ext
      ext q
      fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [rootOperator, hr, WordRelations.rootDividedPower_simple, eDividedPower_one,
      reindex_specialize', reindex_middle1]
    exact middle1_cast
  · change reindex (rootOperator m (testRoot 1)) = testOperator 1
    have hr : testRoot 1 = (typeF4RootPairing_baseEquiv 2 : typeF4Roots) := by
      apply Subtype.ext
      ext q
      fin_cases q <;> norm_num [testRoot, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [rootOperator, hr, WordRelations.rootDividedPower_simple, eDividedPower_one,
      reindex_specialize', reindex_middle2]
    exact middle2_cast
  · change reindex (rootOperator m (testRoot 2)) = testOperator 2
    have hr : reflectionWord (P := typeF4RootPairing)
        [typeF4RootPairing_baseEquiv 0] (typeF4RootPairing_baseEquiv 1) = testRoot 2 := by
      apply typeF4RootPairing.root.injective
      simp only [reflectionWord, typeF4RootPairing.root_reflectionPerm,
        typeF4RootPairing.reflection_apply_root]
      rw [typeF4RootPairing_pairing]
      ext q
      fin_cases q <;> norm_num [testRoot, typeF4CorootScale_simpleRoot,
        dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [rootOperator, WordRelations.rootDividedPower_of_pos_transport _
      (testRoot_positive 2) [typeF4RootPairing_baseEquiv 0]
      (typeF4RootPairing_baseEquiv 1) hr,
      eDividedPower_one, specializeMatrix_transportedMatrix]
    simp only [titsWord, titsWordInv_cons, titsWordInv_nil, mul_one, one_mul,
      tits_inv_cast, map_mul, reindex_specialize', reindex_tits0, reindex_middle1, middleTable1_sparse]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← matrix_mul, ← matrix_mul]
    exact conjugate0_cast
  · change reindex (rootOperator m (testRoot 3)) = testOperator 3
    have hr : reflectionWord (P := typeF4RootPairing)
        [typeF4RootPairing_baseEquiv 3] (typeF4RootPairing_baseEquiv 2) = testRoot 3 := by
      apply typeF4RootPairing.root.injective
      simp only [reflectionWord, typeF4RootPairing.root_reflectionPerm,
        typeF4RootPairing.reflection_apply_root]
      rw [typeF4RootPairing_pairing]
      ext q
      fin_cases q <;> norm_num [testRoot, typeF4CorootScale_simpleRoot,
        dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, typeF4RootPairing_root, typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val, typeF4SimpleRoot, root, realCoord, coord]
    rw [rootOperator, WordRelations.rootDividedPower_of_pos_transport _
      (testRoot_positive 3) [typeF4RootPairing_baseEquiv 3]
      (typeF4RootPairing_baseEquiv 2) hr,
      eDividedPower_one, specializeMatrix_transportedMatrix]
    simp only [titsWord, titsWordInv_cons, titsWordInv_nil, mul_one, one_mul,
      tits_inv_cast, map_mul, reindex_specialize', reindex_tits3, reindex_middle2, middleTable2_sparse]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← matrix_mul, ← matrix_mul]
    exact conjugate3_cast

end ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
