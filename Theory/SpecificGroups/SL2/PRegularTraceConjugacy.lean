module
public import Theory.LinearAlgebra.MatrixTwoCentralizerDeterminant
public import Theory.LinearAlgebra.MatrixTwoCyclicIntertwiner
public import Theory.LinearAlgebra.MatrixPrimeToCharacteristicScalar
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Trace classifies p-regular SL2 conjugacy

Over a finite field of characteristic p, two elements of SL2 whose orders
are not divisible by p are conjugate in SL2 precisely when their traces agree.
The characteristic-two case and the field of order three are included.

At nonzero discriminant, cyclic bases first give a GL2 intertwiner. A
commuting matrix of its inverse determinant corrects it to determinant one.
At zero discriminant, subtracting the repeated eigenvalue gives a square-zero
matrix. Prime-to-characteristic finite order forces this nilpotent part to
vanish, so equal traces give the same scalar matrix. This is the injectivity
step of the p-regular class count used to exhaust the SL2 simple modules.
-/

namespace Matrix.SpecialLinearGroup
variable {K : Type*} [Field K]

private theorem square_sub_scalar_zero (A : Matrix (Fin 2) (Fin 2) K) (r : K)
    (ht : Matrix.trace A = 2 * r) (hd : Matrix.det A = r ^ 2) :
    (A - r • 1) ^ 2 = 0 := by
  simp only [Matrix.trace_fin_two] at ht
  simp only [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination A 0 0 * ht - hd
  · linear_combination A 0 1 * ht
  · linear_combination A 1 0 * ht
  · linear_combination A 1 1 * ht - hd

private theorem eq_scalar_of_trace_sq_eq_four
    {p : ℕ} [CharP K p] (A : SpecialLinearGroup (Fin 2) K)
    (hp : ¬ p ∣ orderOf A) (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) ^ 2 = 4) :
    (A : Matrix (Fin 2) (Fin 2) K) =
      (if ringChar K = 2 then 1 else Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) / 2) • 1 := by
  classical
  have hpow : (A : Matrix (Fin 2) (Fin 2) K) ^ orderOf A = 1 := by
    simpa only [coe_pow, coe_one] using congrArg
      (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
      (pow_orderOf_eq_one A)
  apply Matrix.eq_scalar_of_isNilpotent_sub_of_pow_eq_one _ _ hp hpow
  refine ⟨2, square_sub_scalar_zero _ _ ?_ ?_⟩
  · split_ifs with hchar
    · have htwo : (2 : K) = 0 := by
        have : CharP K 2 := ringChar.of_eq hchar
        exact CharP.cast_eq_zero K 2
      have hfour : (4 : K) = 0 := by linear_combination 2 * htwo
      rw [hfour] at ht
      have hzero := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ht
      simp [hzero, htwo]
    · field_simp [Ring.two_ne_zero hchar]
  · split_ifs with hchar
    · simp
    · rw [A.property]
      have htwo := Ring.two_ne_zero (R := K) hchar
      have hfour : (4 : K) ≠ 0 := by
        convert mul_ne_zero htwo htwo using 1
        norm_num
      field_simp [htwo, hfour]
      linear_combination -ht

private theorem not_scalar_of_trace_sq_ne_four
    (A : SpecialLinearGroup (Fin 2) K)
    (ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) ^ 2 ≠ 4) :
    ¬ ∃ a : K, (A : Matrix (Fin 2) (Fin 2) K) = a • 1 := by
  rintro ⟨a, ha⟩
  apply ht
  have hd := A.property
  rw [ha] at hd ⊢
  have haa : a ^ 2 = 1 := by
    simpa only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] using hd
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  linear_combination 4 * haa

public theorem isConj_iff_trace_eq_of_pRegular [Finite K]
    {p : ℕ} [CharP K p] (A B : SpecialLinearGroup (Fin 2) K)
    (hAp : ¬ p ∣ orderOf A) (hBp : ¬ p ∣ orderOf B) :
    IsConj A B ↔ Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    rw [← hg, coe_mul, coe_mul, Matrix.trace_mul_cycle]
    rw [← coe_mul, inv_mul_cancel, coe_one, Matrix.one_mul]
  · intro ht
    by_cases hdisc : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) ^ 2 = 4
    · have hA := eq_scalar_of_trace_sq_eq_four A hAp hdisc
      have hB := eq_scalar_of_trace_sq_eq_four B hBp (ht ▸ hdisc)
      have heq : A = B := by
        apply Subtype.ext
        rw [hA, hB, ht]
      exact heq ▸ IsConj.refl A
    · have hAd := not_scalar_of_trace_sq_ne_four A hdisc
      have hBd := not_scalar_of_trace_sq_ne_four B (ht ▸ hdisc)
      obtain ⟨D, hD, hAD⟩ := Matrix.exists_intertwiner_of_trace_eq_det_eq
        (A : Matrix (Fin 2) (Fin 2) K) B hAd hBd ht (A.property.trans B.property.symm)
      obtain ⟨C, hCB, hC⟩ := Matrix.exists_commuting_det_of_trace_sq_ne_four_det
        (B : Matrix (Fin 2) (Fin 2) K) (by simpa only [B.property, mul_one, ← ht] using hdisc)
        (Matrix.det D)⁻¹
      let g : SpecialLinearGroup (Fin 2) K :=
        ⟨D * C, by rw [Matrix.det_mul, hC]; exact mul_inv_cancel₀ hD⟩
      have hAg : A * g = g * B := by
        apply Subtype.ext
        change (A : Matrix (Fin 2) (Fin 2) K) * (D * C) = (D * C) * B
        rw [← Matrix.mul_assoc, hAD, Matrix.mul_assoc, ← hCB, ← Matrix.mul_assoc]
      exact (isConj_iff.mpr ⟨g, mul_inv_eq_iff_eq_mul.mpr hAg.symm⟩).symm

end Matrix.SpecialLinearGroup
