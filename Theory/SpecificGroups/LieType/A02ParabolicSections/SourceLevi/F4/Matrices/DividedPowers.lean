module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.Operators
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues

/-!
# The eight simple F4 root matrices at parameter one

The middle-root operator tables supply their integral divided powers through
factorial identities over the torsion-free integral lattice. The end-root
comparisons are already proved in the imported trace calculation. Reindexing
therefore identifies all eight actual signed simple curves with explicit
integral matrices before specialization to any coefficient ring.

Source: the integral Geck construction; GLS3 §1.12 and §2.6, applied to the
binary symplectic Levi used in Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
namespace Theory.SpecificGroups.LieType.SourceLevi.F4.Matrices.DividedPowers
open Operators
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
def positive1Quadratic : Sparse :=
  [(34,33,1)]

def negative1Linear : Sparse :=
  [(1,34,1), (8,10,1), (11,9,1), (16,20,1), (18,22,1), (21,17,1), (23,19,1), (24,28,1), (26,30,1), (29,25,1), (31,27,1), (33,0,1), (33,1,2), (33,2,2), (37,38,1), (41,42,1), (45,46,1), (49,50,1)]

def negative1Quadratic : Sparse :=
  [(33,34,1)]

theorem fMatrix_1 :
    reindex (fMatrix (typeF4RootPairing_baseEquiv 1)) = matrix negative1Linear := by
  rw [reindex_fMatrix, eMatrix_1]
  decide +kernel

def positive2Quadratic : Sparse :=
  [(11,10,1), (21,20,1), (23,22,1), (29,28,1), (31,30,1), (33,32,1), (35,34,1)]

def negative2Linear : Sparse :=
  [(2,11,1), (4,21,1), (5,23,1), (6,29,1), (7,31,1), (8,33,1), (9,35,1), (10,1,1), (10,2,2), (10,3,1), (20,4,2), (22,5,2), (28,6,2), (30,7,2), (32,8,2), (34,9,2), (36,37,1), (38,39,1), (40,41,1), (42,43,1), (44,45,1), (46,47,1), (48,49,1), (50,51,1)]

def negative2Quadratic : Sparse :=
  [(10,11,1), (20,21,1), (22,23,1), (28,29,1), (30,31,1), (32,33,1), (34,35,1)]

theorem fMatrix_2 :
    reindex (fMatrix (typeF4RootPairing_baseEquiv 2)) = matrix negative2Linear := by
  rw [reindex_fMatrix, eMatrix_2]
  decide +kernel

private theorem cancel_matrix_nsmul {n : ℕ} (hn : n ≠ 0)
    {A B : Matrix (Fin 52) (Fin 52) ℤ} (h : n • A = n • B) : A = B := by
  ext r c
  apply nsmul_right_injective hn
  exact congrArg (fun C : Matrix (Fin 52) (Fin 52) ℤ => C r c) h

private theorem quadratic (A Q D : Matrix (Fin 52) (Fin 52) ℤ)
    (h : A ^ 2 = (2 : ℕ) • D) (hq : A ^ 2 = (2 : ℕ) • Q) : D = Q :=
  cancel_matrix_nsmul (by decide) (h.symm.trans hq)

private theorem cubic (A D : Matrix (Fin 52) (Fin 52) ℤ)
    (h : A ^ 3 = (6 : ℕ) • D) (hz : A ^ 3 = 0) : D = 0 := by
  apply cancel_matrix_nsmul (by decide : (6 : ℕ) ≠ 0)
  simpa only [nsmul_zero] using h.symm.trans hz

theorem eDividedPower_1_two :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 1) 2) =
      matrix positive1Quadratic := by
  have h := congrArg (reindex (S := ℤ))
    (eMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 1) 2)
  simp only [map_pow, map_nsmul, eMatrix_1] at h
  apply quadratic (matrix positive1Linear) _ _ h
  rw [pow_two, ← matrix_mul]
  decide +kernel

theorem eDividedPower_1_three :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 1) 3) = 0 := by
  have h := congrArg (reindex (S := ℤ))
    (eMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 1) 3)
  simp only [map_pow, map_nsmul, eMatrix_1] at h
  apply cubic (matrix positive1Linear) _ h
  rw [pow_succ, pow_two, ← matrix_mul, ← matrix_mul]
  have hz : sparseMul (sparseMul positive1Linear positive1Linear) positive1Linear = [] := by
    decide +kernel
  rw [hz, matrix_nil]

theorem fDividedPower_1_two :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 1) 2) =
      matrix negative1Quadratic := by
  have h := congrArg (reindex (S := ℤ))
    (fMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 1) 2)
  simp only [map_pow, map_nsmul, fMatrix_1] at h
  apply quadratic (matrix negative1Linear) _ _ h
  rw [pow_two, ← matrix_mul]
  decide +kernel

theorem fDividedPower_1_three :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 1) 3) = 0 := by
  have h := congrArg (reindex (S := ℤ))
    (fMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 1) 3)
  simp only [map_pow, map_nsmul, fMatrix_1] at h
  apply cubic (matrix negative1Linear) _ h
  rw [pow_succ, pow_two, ← matrix_mul, ← matrix_mul]
  have hz : sparseMul (sparseMul negative1Linear negative1Linear) negative1Linear = [] := by
    decide +kernel
  rw [hz, matrix_nil]

theorem eDividedPower_2_two :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 2) 2) =
      matrix positive2Quadratic := by
  have h := congrArg (reindex (S := ℤ))
    (eMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 2) 2)
  simp only [map_pow, map_nsmul, eMatrix_2] at h
  apply quadratic (matrix positive2Linear) _ _ h
  rw [pow_two, ← matrix_mul]
  decide +kernel

theorem eDividedPower_2_three :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 2) 3) = 0 := by
  have h := congrArg (reindex (S := ℤ))
    (eMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 2) 3)
  simp only [map_pow, map_nsmul, eMatrix_2] at h
  apply cubic (matrix positive2Linear) _ h
  rw [pow_succ, pow_two, ← matrix_mul, ← matrix_mul]
  have hz : sparseMul (sparseMul positive2Linear positive2Linear) positive2Linear = [] := by
    decide +kernel
  rw [hz, matrix_nil]

theorem fDividedPower_2_two :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 2) 2) =
      matrix negative2Quadratic := by
  have h := congrArg (reindex (S := ℤ))
    (fMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 2) 2)
  simp only [map_pow, map_nsmul, fMatrix_2] at h
  apply quadratic (matrix negative2Linear) _ _ h
  rw [pow_two, ← matrix_mul]
  decide +kernel

theorem fDividedPower_2_three :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 2) 3) = 0 := by
  have h := congrArg (reindex (S := ℤ))
    (fMatrix_pow_eq_factorial_smul (typeF4RootPairing_baseEquiv 2) 3)
  simp only [map_pow, map_nsmul, fMatrix_2] at h
  apply cubic (matrix negative2Linear) _ h
  rw [pow_succ, pow_two, ← matrix_mul, ← matrix_mul]
  have hz : sparseMul (sparseMul negative2Linear negative2Linear) negative2Linear = [] := by
    decide +kernel
  rw [hz, matrix_nil]

end
end Theory.SpecificGroups.LieType.SourceLevi.F4.Matrices.DividedPowers
