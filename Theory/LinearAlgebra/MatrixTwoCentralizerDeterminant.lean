module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Prescribed determinants in two-dimensional centralizers

Over a finite field, the centralizer of a two-dimensional matrix with
nonzero characteristic-polynomial discriminant contains a matrix of every
prescribed determinant. A nonzero prescribed determinant therefore gives
an invertible centralizing matrix. This is the determinant correction
needed to turn GL2 conjugacy of regular semisimple matrices into SL2
conjugacy in the p-regular conjugacy-class count.

For C=aI+bA the determinant is a binary quadratic form. In characteristic
two every scalar is a square. Otherwise completing the square reduces to
the finite-field fact that two quadratic value sets must meet. The latter
is Mathlib's `FiniteField.exists_root_sum_quadratic`; the discriminant
hypothesis ensures its second polynomial really has degree two.
-/

namespace Matrix
variable {K : Type*} [Field K] [Finite K]

private theorem quadratic_det_surjective (t d z : K) (hdisc : t ^ 2 ≠ 4 * d) :
    ∃ a b : K, a ^ 2 + t * a * b + d * b ^ 2 = z := by
  classical
  by_cases hchar : ringChar K = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two hchar z
    exact ⟨a, 0, by simpa [pow_two] using ha.symm⟩
  · let : Fintype K := Fintype.ofFinite K
    have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
    have hfour : (4 : K) ≠ 0 := by
      convert mul_ne_zero htwo htwo using 1
      norm_num
    let D := d - t ^ 2 / 4
    have hD : D ≠ 0 := by
      intro hz
      apply hdisc
      dsimp [D] at hz
      field_simp [hfour] at hz
      linear_combination -hz
    let f : Polynomial K := Polynomial.X ^ 2
    let g : Polynomial K := Polynomial.C D * Polynomial.X ^ 2 - Polynomial.C z
    have hf : f.degree = 2 := Polynomial.degree_X_pow 2
    have hg : g.degree = 2 := by
      rw [show g = Polynomial.C D * Polynomial.X ^ 2 - Polynomial.C z from rfl,
        Polynomial.degree_sub_eq_left_of_degree_lt]
      · exact Polynomial.degree_C_mul_X_pow 2 hD
      · rw [Polynomial.degree_C_mul_X_pow 2 hD]
        exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    obtain ⟨u, b, h⟩ := FiniteField.exists_root_sum_quadratic hf hg
      (FiniteField.odd_card_of_char_ne_two hchar)
    have heq : u ^ 2 + D * b ^ 2 = z := by
      simpa only [f, g, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        ← add_sub_assoc, sub_eq_zero] using h
    refine ⟨u - t / 2 * b, b, ?_⟩
    rw [← heq]
    dsimp [D]
    field_simp [htwo, hfour]
    ring

public theorem exists_commuting_det_of_trace_sq_ne_four_det
    (A : Matrix (Fin 2) (Fin 2) K)
    (hA : trace A ^ 2 ≠ 4 * det A) (d : K) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, C * A = A * C ∧ det C = d := by
  obtain ⟨a, b, hab⟩ := quadratic_det_surjective (trace A) (det A) d hA
  refine ⟨a • 1 + b • A, ?_, ?_⟩
  · simp [add_mul, mul_add]
  · convert hab using 1
    simp [det_fin_two, trace_fin_two]
    ring

end Matrix
