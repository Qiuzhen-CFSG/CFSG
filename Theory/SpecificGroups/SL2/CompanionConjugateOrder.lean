module
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Mathlib.Tactic

/-!
# Order of the companion-matrix conjugate product

For a finite odd field of cardinality q>5 and a primitive unit ell, let
`a=[[0,1],[-1,alpha]]` and `u=diag(ell⁻¹,ell)` be actual SL2 matrices.
Then `u⁻¹*a*u*a⁻¹` has order (q-1)/2, for every alpha. Matrix equations
on the supplied SL2 elements retain the source's chosen matrices without
introducing replacement group or field definitions.

The source, ABG II.6 Proposition 1 proof (article p.60, PDF p.61), prints
two incorrect formulas: the word `u⁻¹*a*u*a` omits the last inverse, and
the asserted product is printed as diagonal. Direct multiplication instead
gives `[[ell²,0],[alpha*(1-ell⁻²),ell⁻²]]`, recorded explicitly below.
Since primitive ell has order q-1>4, its two diagonal entries are distinct.
A determinant-one lower transvection therefore diagonalizes this actual
triangular matrix. Conjugation preserves order; the injective diagonal map
identifies the diagonal order with the order of ell², namely (q-1)/2.
Thus the source's order conclusion is preserved with both computations
repaired. No false diagonal-product identity is assumed.
-/

open scoped Matrix

namespace Matrix.SpecialLinearGroup
variable {K : Type*} [Field K]

/-- The corrected triangular product, including the lower-left term
omitted from the printed ABG computation. -/
public theorem companion_conjugate_product_val
    (ell : Kˣ) (α : K) (a u : SpecialLinearGroup (Fin 2) K)
    (ha : a.val = !![0, 1; -1, α])
    (hu : u.val = !![((ell : K)⁻¹), 0; 0, (ell : K)]) :
    (u⁻¹ * a * u * a⁻¹).val =
      !![(ell : K) ^ 2, 0; α * (1 - ((ell : K) ^ 2)⁻¹), ((ell : K) ^ 2)⁻¹] := by
  simp only [coe_mul, coe_inv, ha, hu, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

private theorem diagonal_unit_order (b : Kˣ) :
    orderOf (diag2 (b : K) b.ne_zero) = orderOf b := by
  have he : toGL (diag2 (b : K) b.ne_zero) =
      GeneralLinearGroup.diagonalPair K (b, b⁻¹) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2_coe', GeneralLinearGroup.diagonalPair]
  rw [← orderOf_injective toGL toGL_injective, he,
    orderOf_injective (GeneralLinearGroup.diagonalPair K)
      (GeneralLinearGroup.diagonalPair_injective K),
    Prod.orderOf_mk, orderOf_inv, Nat.lcm_self]

/-- The source order conclusion for the corrected actual SL2 product. -/
public theorem companion_conjugate_product_order [Finite K]
    (hodd : Odd (Nat.card K)) (hq : 5 < Nat.card K)
    (ell : Kˣ) (hell : orderOf ell = Nat.card K - 1) (α : K)
    (a u : SpecialLinearGroup (Fin 2) K)
    (ha : a.val = !![0, 1; -1, α])
    (hu : u.val = !![((ell : K)⁻¹), 0; 0, (ell : K)]) :
    orderOf (u⁻¹ * a * u * a⁻¹) = (Nat.card K - 1) / 2 := by
  have hdist : (ell : K) ^ 2 ≠ ((ell : K) ^ 2)⁻¹ := by
    intro h
    have hs : (ell ^ 2 : Kˣ) = (ell ^ 2)⁻¹ := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using h
    have hf : ell ^ 4 = 1 := by
      calc
        ell ^ 4 = (ell ^ 2) * (ell ^ 2) := by group
        _ = (ell ^ 2) * (ell ^ 2)⁻¹ := congrArg ((ell ^ 2) * ·) hs
        _ = 1 := mul_inv_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hf
    rw [hell] at hd
    have := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  let t := α * (1 - ((ell : K) ^ 2)⁻¹) / ((ell : K) ^ 2 - ((ell : K) ^ 2)⁻¹)
  let C := transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t
  let D := diag2 ((ell ^ 2 : Kˣ) : K) (ell ^ 2).ne_zero
  have ht : t * ((ell : K) ^ 2 - ((ell : K) ^ 2)⁻¹) =
      α * (1 - ((ell : K) ^ 2)⁻¹) := div_mul_cancel₀ _ (sub_ne_zero.mpr hdist)
  have hdiag : C * D = (u⁻¹ * a * u * a⁻¹) * C := by
    apply Subtype.ext
    change C.val * D.val = (u⁻¹ * a * u * a⁻¹).val * C.val
    rw [companion_conjugate_product_val ell α a u ha hu]
    simp only [C, D, transvection_coe, diag2_coe', Units.val_pow_eq_pow_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ht
  have ho : orderOf D = orderOf (u⁻¹ * a * u * a⁻¹) :=
    SemiconjBy.orderOf_eq C hdiag
  rw [← ho, diagonal_unit_order]
  have htwo : 2 ∣ orderOf ell := by
    rw [hell]
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp
  rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) htwo, hell]

end Matrix.SpecialLinearGroup

