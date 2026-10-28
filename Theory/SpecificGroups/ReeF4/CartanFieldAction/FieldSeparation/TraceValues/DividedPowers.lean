module

public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Operators
/-!
# Divided powers of the two end-root operators

Root negation gives the negative operator tables from the certified positive
ones. Sparse multiplication checks their squares and the vanishing of their
cubes. The integral factorial identities, and torsion-freeness over ℤ, then
identify the actual quadratic and cubic divided powers. Thus the subsequent
trace calculation specializes the actual Geck exponentials over any ring.

Source: the integral divided-power construction in `IntegralGeckConstruction.lean`;
GLS3 §1.12 and Table 2.4, type VI.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.Cartan.FieldSeparation.TraceValues
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

def flipIndex (c : Fin 52) : Fin 52 :=
  match c.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | 8 => 9
  | 9 => 8
  | 10 => 11
  | 11 => 10
  | 12 => 15
  | 13 => 14
  | 14 => 13
  | 15 => 12
  | 16 => 19
  | 17 => 18
  | 18 => 17
  | 19 => 16
  | 20 => 23
  | 21 => 22
  | 22 => 21
  | 23 => 20
  | 24 => 27
  | 25 => 26
  | 26 => 25
  | 27 => 24
  | 28 => 31
  | 29 => 30
  | 30 => 29
  | 31 => 28
  | 32 => 35
  | 33 => 34
  | 34 => 33
  | 35 => 32
  | 36 => 51
  | 37 => 50
  | 38 => 49
  | 39 => 48
  | 40 => 47
  | 41 => 46
  | 42 => 45
  | 43 => 44
  | 44 => 43
  | 45 => 42
  | 46 => 41
  | 47 => 40
  | 48 => 39
  | 49 => 38
  | 50 => 37
  | _ => 36

private lemma root_neg_of_coord (r q : Fin 48) (h : coord q = -coord r) :
    root q = -root r := by
  apply typeF4RootPairing.root.injective
  rw [root_neg_value]
  ext k
  change (coord q k : ℝ) / 2 = -((coord r k : ℝ) / 2)
  have hk := congrFun h k
  change coord q k = -coord r k at hk
  rw [hk, Int.cast_neg, neg_div]

lemma basisEquiv_flip (c : Fin 52) : basisEquiv (flipIndex c) = flip (basisEquiv c) := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · change Sum.inr (root 1) = (Sum.inr (-root 0) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 0) = (Sum.inr (-root 1) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 3) = (Sum.inr (-root 2) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 2) = (Sum.inr (-root 3) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 5) = (Sum.inr (-root 4) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 4) = (Sum.inr (-root 5) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 7) = (Sum.inr (-root 6) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 6) = (Sum.inr (-root 7) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 11) = (Sum.inr (-root 8) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 10) = (Sum.inr (-root 9) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 9) = (Sum.inr (-root 10) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 8) = (Sum.inr (-root 11) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 15) = (Sum.inr (-root 12) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 14) = (Sum.inr (-root 13) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 13) = (Sum.inr (-root 14) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 12) = (Sum.inr (-root 15) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 19) = (Sum.inr (-root 16) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 18) = (Sum.inr (-root 17) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 17) = (Sum.inr (-root 18) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 16) = (Sum.inr (-root 19) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 23) = (Sum.inr (-root 20) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 22) = (Sum.inr (-root 21) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 21) = (Sum.inr (-root 22) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 20) = (Sum.inr (-root 23) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 27) = (Sum.inr (-root 24) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 26) = (Sum.inr (-root 25) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 25) = (Sum.inr (-root 26) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 24) = (Sum.inr (-root 27) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 31) = (Sum.inr (-root 28) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 30) = (Sum.inr (-root 29) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 29) = (Sum.inr (-root 30) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 28) = (Sum.inr (-root 31) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 47) = (Sum.inr (-root 32) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 46) = (Sum.inr (-root 33) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 45) = (Sum.inr (-root 34) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 44) = (Sum.inr (-root 35) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 43) = (Sum.inr (-root 36) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 42) = (Sum.inr (-root 37) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 41) = (Sum.inr (-root 38) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 40) = (Sum.inr (-root 39) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 39) = (Sum.inr (-root 40) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 38) = (Sum.inr (-root 41) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 37) = (Sum.inr (-root 42) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 36) = (Sum.inr (-root 43) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 35) = (Sum.inr (-root 44) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 34) = (Sum.inr (-root 45) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 33) = (Sum.inr (-root 46) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel
  · change Sum.inr (root 32) = (Sum.inr (-root 47) : Basis)
    congr 1
    apply root_neg_of_coord
    decide +kernel

lemma reindex_fMatrix (i : typeF4RootPairing_base.support) :
    reindex (fMatrix i) = (reindex (eMatrix i)).submatrix flipIndex flipIndex := by
  ext r c
  simp only [Matrix.submatrix_apply, reindex_apply, basisEquiv_flip]
  exact fMatrix_flip i _ _

lemma fMatrix_0 :
    reindex (fMatrix (typeF4RootPairing_baseEquiv 0)) = matrix negative0Linear := by
  rw [reindex_fMatrix, eMatrix_0]
  decide +kernel

lemma fMatrix_3 :
    reindex (fMatrix (typeF4RootPairing_baseEquiv 3)) = matrix negative3Linear := by
  rw [reindex_fMatrix, eMatrix_3]
  decide +kernel

lemma matrix_identity : matrix identityEntries = 1 := by decide +kernel

private lemma quadratic_table (a q : Sparse)
    (h : matrix (sparseMul a a) = (2 : ℕ) • matrix q) :
    matrix a ^ 2 = (2 : ℕ) • matrix q := by
  rw [pow_two, ← matrix_mul]
  exact h

private lemma cubic_table (a : Sparse)
    (h : sparseMul (sparseMul a a) a = []) : matrix a ^ 3 = 0 := by
  rw [pow_succ, pow_two, ← matrix_mul, ← matrix_mul, h, matrix_nil]

private lemma cancel_matrix_nsmul {n : ℕ} (hn : n ≠ 0)
    {A B : Matrix (Fin 52) (Fin 52) ℤ} (h : n • A = n • B) : A = B := by
  ext r c
  apply nsmul_right_injective hn
  exact congrArg (fun C : Matrix (Fin 52) (Fin 52) ℤ => C r c) h

private lemma e_quadratic (i : typeF4RootPairing_base.support) (a q : Sparse)
    (he : reindex (eMatrix i) = matrix a)
    (hq : matrix a ^ 2 = (2 : ℕ) • matrix q) :
    reindex (eDividedPower i 2) = matrix q := by
  have h := congrArg (reindex (S := ℤ)) (eMatrix_pow_eq_factorial_smul i 2)
  simp only [map_pow, map_nsmul, he] at h
  change matrix a ^ 2 = (2 : ℕ) • reindex (eDividedPower i 2) at h
  exact cancel_matrix_nsmul (by decide : (2 : ℕ) ≠ 0) (h.symm.trans hq)

private lemma f_quadratic (i : typeF4RootPairing_base.support) (a q : Sparse)
    (hf : reindex (fMatrix i) = matrix a)
    (hq : matrix a ^ 2 = (2 : ℕ) • matrix q) :
    reindex (fDividedPower i 2) = matrix q := by
  have h := congrArg (reindex (S := ℤ)) (fMatrix_pow_eq_factorial_smul i 2)
  simp only [map_pow, map_nsmul, hf] at h
  change matrix a ^ 2 = (2 : ℕ) • reindex (fDividedPower i 2) at h
  exact cancel_matrix_nsmul (by decide : (2 : ℕ) ≠ 0) (h.symm.trans hq)

private lemma e_cubic (i : typeF4RootPairing_base.support) (a : Sparse)
    (he : reindex (eMatrix i) = matrix a) (hz : matrix a ^ 3 = 0) :
    reindex (eDividedPower i 3) = 0 := by
  have h := congrArg (reindex (S := ℤ)) (eMatrix_pow_eq_factorial_smul i 3)
  simp only [map_pow, map_nsmul, he, hz] at h
  change 0 = (6 : ℕ) • reindex (eDividedPower i 3) at h
  apply cancel_matrix_nsmul (by decide : (6 : ℕ) ≠ 0)
  simpa only [nsmul_zero] using h.symm

private lemma f_cubic (i : typeF4RootPairing_base.support) (a : Sparse)
    (hf : reindex (fMatrix i) = matrix a) (hz : matrix a ^ 3 = 0) :
    reindex (fDividedPower i 3) = 0 := by
  have h := congrArg (reindex (S := ℤ)) (fMatrix_pow_eq_factorial_smul i 3)
  simp only [map_pow, map_nsmul, hf, hz] at h
  change 0 = (6 : ℕ) • reindex (fDividedPower i 3) at h
  apply cancel_matrix_nsmul (by decide : (6 : ℕ) ≠ 0)
  simpa only [nsmul_zero] using h.symm

lemma eDividedPower_0_two :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 0) 2) =
      matrix positive0Quadratic := by
  apply e_quadratic _ positive0Linear _ eMatrix_0
  apply quadratic_table
  decide +kernel

lemma eDividedPower_0_three :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 0) 3) = 0 := by
  apply e_cubic _ positive0Linear eMatrix_0
  apply cubic_table
  decide +kernel

lemma eDividedPower_3_two :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 3) 2) =
      matrix positive3Quadratic := by
  apply e_quadratic _ positive3Linear _ eMatrix_3
  apply quadratic_table
  decide +kernel

lemma eDividedPower_3_three :
    reindex (eDividedPower (typeF4RootPairing_baseEquiv 3) 3) = 0 := by
  apply e_cubic _ positive3Linear eMatrix_3
  apply cubic_table
  decide +kernel

lemma fDividedPower_0_two :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 0) 2) =
      matrix negative0Quadratic := by
  apply f_quadratic _ negative0Linear _ fMatrix_0
  apply quadratic_table
  decide +kernel

lemma fDividedPower_0_three :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 0) 3) = 0 := by
  apply f_cubic _ negative0Linear fMatrix_0
  apply cubic_table
  decide +kernel

lemma fDividedPower_3_two :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 3) 2) =
      matrix negative3Quadratic := by
  apply f_quadratic _ negative3Linear _ fMatrix_3
  apply quadratic_table
  decide +kernel

lemma fDividedPower_3_three :
    reindex (fDividedPower (typeF4RootPairing_baseEquiv 3) 3) = 0 := by
  apply f_cubic _ negative3Linear fMatrix_3
  apply cubic_table
  decide +kernel

end
end ReeF4.Cartan.FieldSeparation.TraceValues
