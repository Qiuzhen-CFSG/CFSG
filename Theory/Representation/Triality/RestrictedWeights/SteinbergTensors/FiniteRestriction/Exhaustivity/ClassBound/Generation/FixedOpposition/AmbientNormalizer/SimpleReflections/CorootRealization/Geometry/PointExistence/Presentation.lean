module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.CharP.Two

/-!
# A characteristic-two rank-one presentation

An additive upper curve, multiplicative diagonal elements and an involution
satisfying the scaling and nonzero Bruhat relations determine a homomorphism
from the actual matrix group SL₂. The proof evaluates the two Bruhat normal
forms, checks right multiplication by an upper transvection and the swap
matrix, and uses transvection induction. No presentation theorem or model
identification is assumed.

This supplies the algebraic construction step for the opposite-root argument
of GLS3, Chapter 1, §1.12 (`refs/KGroup/GLS3/Chapter1.tex`). Its hypotheses are
explicit relations; their validity on an actual root pair is a separate
geometric theorem.
-/

namespace Theory.AlgebraicGroup.BinaryRankOne
variable {k G : Type*} [Field k] [CharP k 2] [Group G]

/-- The additive, diagonal, and Bruhat identities used by the matrix normal form. -/
public structure Relations (x : k → G) (h : k → G) (w : G) : Prop where
  x_zero : x 0 = 1
  x_add : ∀ a b, x (a + b) = x a * x b
  h_one : h 1 = 1
  h_mul : ∀ a b, a ≠ 0 → b ≠ 0 → h (a * b) = h a * h b
  h_x : ∀ a, a ≠ 0 → ∀ b, h a * x b = x (a ^ 2 * b) * h a
  w_sq : w * w = 1
  w_x : ∀ a, a ≠ 0 → w * x a * w = x a⁻¹ * h a⁻¹ * w * x a⁻¹

private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) k

/-- The upper elementary matrix. -/
@[expose] public def upper (t : k) : Matrix.SpecialLinearGroup (Fin 2) k := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t

/-- The lower elementary matrix. -/
@[expose] public def lower (t : k) : Matrix.SpecialLinearGroup (Fin 2) k := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t

private def swap : SL (k := k) := ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private noncomputable def normal (x h : k → G) (w : G) (A : SL (k := k)) : G :=
  by
  classical
  exact if A.1 1 0 = 0 then h (A.1 0 0) * x (A.1 0 1 / A.1 0 0)
  else x (A.1 0 0 / A.1 1 0) * h ((A.1 1 0)⁻¹) * w * x (A.1 1 1 / A.1 1 0)

private lemma det (A : SL (k := k)) : A.1 0 0 * A.1 1 1 + A.1 0 1 * A.1 1 0 = 1 := by
  have hh := A.2
  change Matrix.det A.1 = 1 at hh
  simpa only [Matrix.det_fin_two, CharTwo.sub_eq_add] using hh

omit [CharP k 2] in
private lemma mul_upper (A : SL (k := k)) (t : k) :
    (A * upper t).1 = !![A.1 0 0, A.1 0 0 * t + A.1 0 1;
      A.1 1 0, A.1 1 0 * t + A.1 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]

private lemma mul_swap (A : SL (k := k)) :
    (A * swap).1 = !![A.1 0 1, A.1 0 0; A.1 1 1, A.1 1 0] := by
  ext i j
  change (A.1 * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k)) i j = _
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {x h : k → G} {w : G} (R : Relations x h w)
include R

omit [CharP k 2] in
private lemma normal_one : normal x h w (1 : SL (k := k)) = 1 := by
  simp [normal, R.h_one, R.x_zero]

private lemma normal_mul_upper (A : SL (k := k)) (t : k) :
    normal x h w (A * upper t) = normal x h w A * x t := by
  have hd := det A
  by_cases hc : A.1 1 0 = 0
  · have ha : A.1 0 0 ≠ 0 := by intro ha; simp [hc, ha] at hd
    have hb : (A.1 0 0 * t + A.1 0 1) / A.1 0 0 = A.1 0 1 / A.1 0 0 + t := by field_simp; ring
    simp only [normal]
    rw [mul_upper]
    simp [hc, hb, R.x_add, mul_assoc]
  · have hb : (A.1 1 0 * t + A.1 1 1) / A.1 1 0 = A.1 1 1 / A.1 1 0 + t := by field_simp; ring
    simp only [normal]
    rw [mul_upper]
    simp [hc, hb, R.x_add, mul_assoc]

private lemma formula_swap [DecidableEq k] (a b c d : k) (hd : a * d + b * c = 1) :
    (if d = 0 then h b * x (a / b)
      else x (b / d) * h d⁻¹ * w * x (c / d)) =
    (if c = 0 then h a * x (b / a)
      else x (a / c) * h c⁻¹ * w * x (d / c)) * w := by
  classical
  by_cases hc : c = 0
  · have had : a * d = 1 := by simpa [hc] using hd
    have ha : a ≠ 0 := by intro ha; simp [ha] at had
    have he : d ≠ 0 := by intro he; simp [he] at had
    have hi : (d)⁻¹ = a := by apply inv_eq_of_mul_eq_one_left; exact had
    have hp : b / d = a ^ 2 * (b / a) := by
      rw [div_eq_mul_inv, hi]; field_simp
    simp only [hc, if_pos, zero_div, R.x_zero, mul_one, hi]
    rw [if_neg he, R.h_x _ ha, hp]
  · by_cases he : d = 0
    · have hbc : b * c = 1 := by simpa [he] using hd
      have hb : b ≠ 0 := by intro hb; simp [hb] at hbc
      have hi : (c)⁻¹ = b := by apply inv_eq_of_mul_eq_one_left; exact hbc
      have hp : a / c = b ^ 2 * (a / b) := by
        rw [div_eq_mul_inv, hi]; field_simp
      simp only [he, if_pos, if_neg hc, zero_div, R.x_zero, mul_one, hi]
      rw [R.h_x _ hb, hp]
      simp only [mul_assoc, R.w_sq, mul_one]
    · have hdc : d / c ≠ 0 := div_ne_zero he hc
      have hi : (d / c)⁻¹ = c / d := inv_div _ _
      have hm : (c)⁻¹ * (c / d) = (d)⁻¹ := by field_simp
      have hp : a / c + (c)⁻¹ ^ 2 * (c / d) = b / d := by
        field_simp
        calc
          _ = a * d + (a * d + b * c) := congrArg (a * d + ·) hd.symm
          _ = _ := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add, mul_comm]
      simp only [if_neg hc]
      rw [if_neg he]
      calc
        _ = x (a / c + (c)⁻¹ ^ 2 * (c / d)) *
            h ((c)⁻¹ * (c / d)) * w * x (c / d) := by rw [hp, hm]
        _ = _ := by
          rw [R.h_mul _ _ (inv_ne_zero hc) (div_ne_zero hc he), R.x_add]
          have hx := R.h_x (c)⁻¹ (inv_ne_zero hc) (c / d)
          have hw := R.w_x (d / c) hdc
          rw [hi] at hw
          calc
            _ = x (a / c) * (h (c)⁻¹ * x (c / d)) * h (c / d) * w * x (c / d) := by rw [hx]; simp only [mul_assoc]
            _ = _ := by simp only [mul_assoc] at hw ⊢; rw [← hw]

private lemma normal_mul_swap (A : SL (k := k)) :
    normal x h w (A * swap) = normal x h w A * w := by
  classical
  have hh := formula_swap R (A.1 0 0) (A.1 0 1) (A.1 1 0) (A.1 1 1) (det A)
  unfold normal
  rw [mul_swap]
  exact hh

omit R in
private lemma lower_eq (t : k) : lower t = swap * upper t * swap := by
  apply Subtype.ext
  change (lower t).1 = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k) * (upper t).1 * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, upper, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private lemma normal_mul_lower (A : SL (k := k)) (t : k) :
    normal x h w (A * lower t) = normal x h w A * (w * x t * w) := by
  rw [lower_eq, ← mul_assoc, ← mul_assoc, normal_mul_swap R, normal_mul_upper R, normal_mul_swap R]
  simp only [mul_assoc]

private lemma normal_upper (t : k) : normal x h w (upper t) = x t := by
  simpa only [one_mul, normal_one R] using normal_mul_upper R 1 t

private lemma normal_lower (t : k) : normal x h w (lower t) = w * x t * w := by
  simpa only [one_mul, normal_one R] using normal_mul_lower R 1 t

private lemma normal_mul (A B : SL (k := k)) :
    normal x h w (A * B) = normal x h w A * normal x h w B := by
  have hh : ∀ B : SL (k := k), ∀ A,
      normal x h w (A * B) = normal x h w A * normal x h w B := by
    apply Matrix.SL2.transvection_induction
    · intro i j hij t A
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · change normal x h w (A * upper t) = normal x h w A * normal x h w (upper t)
        rw [normal_mul_upper R, normal_upper R]
      · change normal x h w (A * lower t) = normal x h w A * normal x h w (lower t)
        rw [normal_mul_lower R, normal_lower R]
      · exact (hij rfl).elim
    · intro B C hB hC A
      rw [← mul_assoc, hC, hB, hC, mul_assoc]
  exact hh B A

/-- The homomorphism defined by the two matrix Bruhat cells. -/
public noncomputable def Relations.toHom : Matrix.SpecialLinearGroup (Fin 2) k →* G where
  toFun := normal x h w
  map_one' := normal_one R
  map_mul' := normal_mul R

/-- The constructed homomorphism has the prescribed upper curve. -/
public lemma Relations.toHom_upper (t : k) : R.toHom (upper t) = x t := normal_upper R t

/-- The lower curve is the conjugate of the upper curve by the given involution. -/
public lemma Relations.toHom_lower (t : k) : R.toHom (lower t) = w * x t * w := normal_lower R t

end Theory.AlgebraicGroup.BinaryRankOne
