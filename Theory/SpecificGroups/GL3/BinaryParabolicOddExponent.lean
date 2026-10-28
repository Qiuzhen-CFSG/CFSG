module
public import Theory.SpecificGroups.GL2.BinaryOddExponent
public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Odd exponents of natural GL₃ parabolics in characteristic two

Powers of a matrix preserving the standard point preserve its block shape;
the diagonal blocks are the corresponding powers of a scalar and a GL₂
matrix. Both are killed by q²−1. The remaining upper off-diagonal block
squares to zero, so the resulting unipotent matrix has order dividing two.
Odd order makes it the identity. Reverse transpose gives the plane case.

This is the natural matrix input for the Hermitian torus argument in
Aschbacher–Smith 8.2.3, printed pp.715–716, allowing nonsplit GL₂ blocks.
-/

public noncomputable section
open Matrix
namespace Matrix.GeneralLinearGroup
variable {F : Type*} [Field F]

private def tailBlock (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  M.submatrix Fin.succ Fin.succ

private theorem point_pow (M : Matrix (Fin 3) (Fin 3) F)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (k : ℕ) :
    (M^k) 1 0 = 0 ∧ (M^k) 2 0 = 0 ∧ (M^k) 0 0 = M 0 0 ^ k ∧
      tailBlock (M^k) = tailBlock M ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨by simp,by simp,by simp,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ]
    refine ⟨?_,?_,?_,?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_three, ih.1,h10,h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_three, ih.2.1,h10,h20]
    · simp [Matrix.mul_apply, Fin.sum_univ_three, ih.2.2.1,h10,h20]
    · rw [← ih.2.2.2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [tailBlock,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two,ih.1,ih.2.1]

private theorem point_det (M : Matrix (Fin 3) (Fin 3) F)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) :
    M.det = M 0 0 * (tailBlock M).det := by
  rw [Matrix.det_fin_three,Matrix.det_fin_two]
  simp [tailBlock,h10,h20]
  ring

private def reverseTranspose (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  M.transpose.submatrix Fin.revPerm Fin.revPerm

private theorem reverseTranspose_mul (M N : Matrix (Fin 3) (Fin 3) F) :
    reverseTranspose (M*N) = reverseTranspose N * reverseTranspose M := by
  simp only [reverseTranspose,Matrix.transpose_mul,Matrix.submatrix_mul_equiv]

private theorem reverseTranspose_one : reverseTranspose (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  simp [reverseTranspose]

private theorem reverseTranspose_pow (M : Matrix (Fin 3) (Fin 3) F) (k : ℕ) :
    reverseTranspose (M^k) = reverseTranspose M ^ k := by
  induction k with
  | zero => exact reverseTranspose_one
  | succ k ih => rw [pow_succ,reverseTranspose_mul,ih,←pow_succ']

omit [Field F] in
private theorem reverseTranspose_reverseTranspose (M : Matrix (Fin 3) (Fin 3) F) :
    reverseTranspose (reverseTranspose M) = M := by
  ext i j
  simp [reverseTranspose,Fin.revPerm]

private def dual (A : GL (Fin 3) F) : GL (Fin 3) F where
  val := reverseTranspose A.val
  inv := reverseTranspose A.inv
  val_inv := by rw [← reverseTranspose_mul,A.inv_val,reverseTranspose_one]
  inv_val := by rw [← reverseTranspose_mul,A.val_inv,reverseTranspose_one]

private theorem dual_pow (A : GL (Fin 3) F) (k : ℕ) : dual (A^k) = dual A ^ k :=
  Units.ext (reverseTranspose_pow A.val k)

private theorem dual_one : dual (1 : GL (Fin 3) F) = 1 := Units.ext reverseTranspose_one

private theorem dual_dual (A : GL (Fin 3) F) : dual (dual A) = A :=
  Units.ext (reverseTranspose_reverseTranspose A.val)

private theorem dual_order (A : GL (Fin 3) F) : orderOf (dual A) = orderOf A := by
  have hd (B : GL (Fin 3) F) : orderOf (dual B) ∣ orderOf B :=
    orderOf_dvd_of_pow_eq_one (by rw [←dual_pow,pow_orderOf_eq_one,dual_one])
  exact Nat.dvd_antisymm (hd A) (by simpa only [dual_dual] using hd (dual A))

variable [Finite F] [CharP F 2]

private theorem point_odd_exponent
    (A : GL (Fin 3) F) (ho : Odd (orderOf A))
    (h10 : A.val 1 0 = 0) (h20 : A.val 2 0 = 0) :
    orderOf A ∣ Nat.card F ^ 2 - 1 := by
  let r := Nat.card F ^ 2 - 1
  have hdet : A.val 0 0 * (tailBlock A.val).det ≠ 0 := by
    rw [← point_det A.val h10 h20]
    exact A.det_ne_zero
  have h00 := (mul_ne_zero_iff.mp hdet).1
  let B : GL (Fin 2) F := mkOfDetNeZero (tailBlock A.val) (mul_ne_zero_iff.mp hdet).2
  have hBpow (k : ℕ) : (B ^ k).val = tailBlock ((A ^ k).val) :=
    (point_pow A.val h10 h20 k).2.2.2.symm
  have hB : orderOf B ∣ orderOf A := by
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    rw [hBpow,pow_orderOf_eq_one]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hBr : (B ^ r).val = 1 := by
    rw [orderOf_dvd_iff_pow_eq_one.mp (odd_order_dvd_card_sq_sub_one B (ho.of_dvd_nat hB))]
    rfl
  have h00r : A.val 0 0 ^ r = 1 := by
    let := Fintype.ofFinite F
    have hc : A.val 0 0 ^ (Nat.card F - 1) = 1 := by
      simpa only [Nat.card_eq_fintype_card] using
        FiniteField.pow_card_sub_one_eq_one (A.val 0 0) h00
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_dvd_of_pow_eq_one hc).trans (Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2)
  let C := A ^ r
  obtain ⟨hc10,hc20,hc00,hcb⟩ := point_pow A.val h10 h20 r
  change C.val 1 0 = 0 at hc10
  change C.val 2 0 = 0 at hc20
  change C.val 0 0 = _ at hc00
  rw [h00r] at hc00
  have htail : tailBlock C.val = 1 := (hBpow r).symm.trans hBr
  have hc11 : C.val 1 1 = 1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) htail
  have hc12 : C.val 1 2 = 0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) htail
  have hc21 : C.val 2 1 = 0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) htail
  have hc22 : C.val 2 2 = 1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) htail
  have hc2 : C ^ 2 = 1 := by
    apply Units.ext
    change C.val ^ 2 = 1
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_three,hc00,hc10,hc20,hc11,hc12,hc21,hc22,
        CharTwo.add_self_eq_zero]
  have hoc : Odd (orderOf C) := ho.of_dvd_nat (orderOf_pow_dvd r)
  have hc1 : orderOf C ∣ 1 := (Nat.coprime_two_right.mpr hoc).dvd_of_dvd_mul_right
    (show orderOf C ∣ 1 * 2 by simpa using orderOf_dvd_of_pow_eq_one hc2)
  exact orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hc1))

/-- An odd element preserving the standard point or plane has order dividing
q²−1, including arbitrary off-diagonal blocks and nonsplit Levi factors. -/
theorem binary_parabolic_odd_order_dvd (A : GL (Fin 3) F) (ho : Odd (orderOf A))
    (hp : (A.val 1 0 = 0 ∧ A.val 2 0 = 0) ∨
      (A.val 2 0 = 0 ∧ A.val 2 1 = 0)) : orderOf A ∣ Nat.card F ^ 2 - 1 := by
  rcases hp with ⟨h10,h20⟩ | ⟨h20,h21⟩
  · exact point_odd_exponent A ho h10 h20
  · have h := point_odd_exponent (dual A) (by rwa [dual_order])
      (show (dual A).val 1 0 = 0 from h21) (show (dual A).val 2 0 = 0 from h20)
    rwa [dual_order] at h

end Matrix.GeneralLinearGroup
