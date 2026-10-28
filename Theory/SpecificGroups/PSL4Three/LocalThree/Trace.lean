module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Trace of projective involution lifts in SL₄(3)

For a lift M, write M² = c I with c² = 1. The determinant-one equation
makes its characteristic polynomial X⁴ - t X³ + s X² - c t X + 1,
where t = trace(M). Cayley–Hamilton makes (2 c t) M scalar. Nonzero trace
would make M scalar, contradicting its nonidentity projective image.

The characteristic-polynomial argument adapts the one in the repository's
`ClassicalUnitary/UnitaryFourThree/ElementaryLocal/InvolutionCentralizer/Trace.lean`;
here the inverse equation follows directly from M² = c I.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4) on printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Polynomial
noncomputable section
namespace Matrix.PSL4Three.LocalThree

private theorem charpoly_coeff_one (M : Mat) (hd : M.det = 1)
    (c : ZMod 3) (hc : c ^ 2 = 1) (hsq : M ^ 2 = c • (1 : Mat)) :
    M.charpoly.coeff 1 = -(c * Matrix.trace M) := by
  have hi := Matrix.charpoly_inv M ((Matrix.isUnit_iff_isUnit_det M).mpr (hd ▸ isUnit_one))
  have hcoeff := congrArg (fun p : Polynomial (ZMod 3) => p.coeff 3) hi
  rw [hd] at hcoeff
  norm_num at hcoeff
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse,
    Matrix.charpoly_natDegree_eq_dim] at hcoeff
  have ht := Matrix.trace_eq_neg_charpoly_coeff M⁻¹
  norm_num [Polynomial.revAt] at hcoeff ht
  have hleft : (c • M) * M = 1 := by
    rw [smul_mul_assoc, ← pow_two, hsq, smul_smul, ← pow_two, hc, one_smul]
  rw [hcoeff, Matrix.inv_eq_left_inv hleft, Matrix.trace_smul, smul_eq_mul] at ht
  exact neg_eq_iff_eq_neg.mp ht.symm

private theorem quartic (M : Mat) :
    M.charpoly = X ^ 4 + C (M.charpoly.coeff 3) * X ^ 3 +
      C (M.charpoly.coeff 2) * X ^ 2 + C (M.charpoly.coeff 1) * X +
      C (M.charpoly.coeff 0) := by
  have hd : M.charpoly.natDegree = 4 := M.charpoly_natDegree_eq_dim
  have hcoeff : M.charpoly.coeff 4 = 1 := by
    simpa only [hd] using M.charpoly_monic.coeff_natDegree
  conv_lhs => rw [M.charpoly.as_sum_range_C_mul_X_pow, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, hcoeff, C_1, one_mul]
  ring

private theorem scalar_of_square_scalar_of_trace_ne_zero (M : Mat)
    (hd : M.det = 1) (c : ZMod 3) (hc : c ^ 2 = 1)
    (hsq : M ^ 2 = c • (1 : Mat)) (ht : Matrix.trace M ≠ 0) :
    ∃ a : ZMod 3, M = a • (1 : Mat) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hcube : M ^ 3 = c • M := by
    rw [pow_succ M 2, hsq, smul_mul_assoc, one_mul]
  have hfour : M ^ 4 = c ^ 2 • (1 : Mat) := by
    rw [show M ^ 4 = M ^ 2 * M ^ 2 from pow_add M 2 2, hsq,
      smul_mul_smul, one_mul, pow_two]
  have h0 := Matrix.det_eq_sign_charpoly_coeff M
  have h3 := Matrix.trace_eq_neg_charpoly_coeff M
  norm_num at h0 h3
  have hp0 : M.charpoly.coeff 0 = 1 := h0.symm.trans hd
  have hp3 : M.charpoly.coeff 3 = -Matrix.trace M := neg_eq_iff_eq_neg.mp h3.symm
  have h := M.aeval_self_charpoly
  rw [quartic, hp0, hp3, charpoly_coeff_one M hd c hc hsq] at h
  have heq : M ^ 4 - (Matrix.trace M) • M ^ 3 + (M.charpoly.coeff 2) • M ^ 2 -
      (c * Matrix.trace M) • M + 1 = 0 := by
    simpa only [map_add, map_mul, map_pow, aeval_X, aeval_C, C_1,
      map_one, ← Algebra.smul_def, neg_smul, ← sub_eq_add_neg] using h
  rw [hcube, hfour, hsq, smul_smul, smul_smul] at heq
  have hb : 2 * c * Matrix.trace M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by decide) hc0) ht
  have he : (2 * c * Matrix.trace M) • M =
      (c ^ 2 + M.charpoly.coeff 2 * c + 1) • (1 : Mat) := by
    apply Matrix.ext
    intro i j
    have hij := congrArg (fun A : Mat => A i j) heq
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at hij ⊢
    linear_combination -hij
  refine ⟨(2 * c * Matrix.trace M)⁻¹ * (c ^ 2 + M.charpoly.coeff 2 * c + 1), ?_⟩
  have he' := congrArg (fun A : Mat => (2 * c * Matrix.trace M)⁻¹ • A) he
  simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using he'

public theorem trace_eq_zero_of_projective_involution (g : SL)
    (hne : project g ≠ 1) (hsq : (project g)^2 = 1) : Matrix.trace (g : Mat) = 0 := by
  by_contra ht
  obtain ⟨c, hc, he⟩ := square_scalar g hsq
  obtain ⟨a, ha⟩ := scalar_of_square_scalar_of_trace_ne_zero g g.property c hc he ht
  exact hne (project_eq_one_of_scalar g a ha)
end Matrix.PSL4Three.LocalThree
