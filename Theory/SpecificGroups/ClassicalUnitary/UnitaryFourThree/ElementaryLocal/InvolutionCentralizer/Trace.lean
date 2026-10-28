module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.ScalarKernel
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Trace of projective involution lifts in SU₄(3)

A lift of a projective involution has square `c I`, where `c` is a fourth
root of unity. Write `t` for its trace. Its determinant-one and Hermitian
equations give characteristic polynomial `X⁴ - t X³ + s X² - star(t) X + 1`.
In characteristic three, `trace(M³) = trace(M)³`, hence `star(t) = c t`.
Cayley–Hamilton therefore makes `(2 c t) M` scalar. If `t` were nonzero,
`M` itself would be scalar, contrary to its nonidentity projective image.

The proof uses the entire order-four scalar kernel of the actual SU image
in PGL. The projection in `IsotropicStabilizers.ScalarKernel` is definitionally
the model projection. No eigenspace classification or group-order assumption
is needed for this trace calculation.

This is a local linear-algebra input for the PSU₄(3) case of
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`,
restated as Theorem 0.1.1(4) on printed p.482. The SU/PSU conventions are
those of GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

open Matrix Polynomial BenderSuzuki.MatrixGroups

noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer

private abbrev F := FiniteField.Nine
private abbrev Mat := Matrix (Fin 4) (Fin 4) F

private theorem trace_cube (M : Mat) : Matrix.trace (M ^ 3) = (Matrix.trace M) ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring_nf
  simp only [show (3 : F) = 0 by decide, show (6 : F) = 0 by decide,
    mul_zero, zero_add, add_zero]

private theorem charpoly_coeff_one (M : Mat) (hd : M.det = 1)
    (hu : M.conjTranspose * M = 1) :
    M.charpoly.coeff 1 = -star (Matrix.trace M) := by
  have hi := Matrix.charpoly_inv M ((Matrix.isUnit_iff_isUnit_det M).mpr (hd ▸ isUnit_one))
  have hc := congrArg (fun p : Polynomial F => p.coeff 3) hi
  rw [hd] at hc
  norm_num at hc
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse,
    Matrix.charpoly_natDegree_eq_dim] at hc
  have ht := Matrix.trace_eq_neg_charpoly_coeff M⁻¹
  norm_num [Polynomial.revAt] at hc ht
  rw [hc, Matrix.inv_eq_left_inv hu] at ht
  have hadj : Matrix.trace M.conjTranspose = star (Matrix.trace M) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.conjTranspose_apply, star_sum]
  rw [hadj] at ht
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

private theorem cayley (M : Mat) (hd : M.det = 1) (hu : M.conjTranspose * M = 1) :
    M ^ 4 - (Matrix.trace M) • M ^ 3 + (M.charpoly.coeff 2) • M ^ 2 -
      star (Matrix.trace M) • M + 1 = 0 := by
  have h0 := Matrix.det_eq_sign_charpoly_coeff M
  have h3 := Matrix.trace_eq_neg_charpoly_coeff M
  norm_num at h0 h3
  have hc0 : M.charpoly.coeff 0 = 1 := h0.symm.trans hd
  have hc3 : M.charpoly.coeff 3 = -Matrix.trace M := by
    exact neg_eq_iff_eq_neg.mp h3.symm
  have h := M.aeval_self_charpoly
  rw [quartic, hc0, hc3, charpoly_coeff_one M hd hu] at h
  simpa only [map_add, map_mul, map_pow, aeval_X, aeval_C, C_1,
    map_one, ← Algebra.smul_def, neg_smul, ← sub_eq_add_neg] using h

private theorem scalar_of_square_scalar_of_trace_ne_zero (M : Mat)
    (hd : M.det = 1) (hu : M.conjTranspose * M = 1)
    (c : F) (hc : c ≠ 0) (hsq : M ^ 2 = c • (1 : Mat))
    (ht : Matrix.trace M ≠ 0) :
    ∃ a : F, M = a • (1 : Mat) := by
  have hcube : M ^ 3 = c • M := by
    rw [pow_succ M 2, hsq, smul_mul_assoc, one_mul]
  have hfour : M ^ 4 = c ^ 2 • (1 : Mat) := by
    rw [show M ^ 4 = M ^ 2 * M ^ 2 from pow_add M 2 2, hsq,
      smul_mul_smul, one_mul, pow_two]
  have hstar : star (Matrix.trace M) = c * Matrix.trace M := by
    rw [FiniteField.Nine.star_eq_cube, ← trace_cube, hcube, Matrix.trace_smul, smul_eq_mul]
  have hb : c * Matrix.trace M + star (Matrix.trace M) ≠ 0 := by
    rw [hstar, ← two_mul]
    exact mul_ne_zero (by decide) (mul_ne_zero hc ht)
  have h := cayley M hd hu
  rw [hcube, hfour, hsq, smul_smul, smul_smul] at h
  have he : (c * Matrix.trace M + star (Matrix.trace M)) • M =
      (c ^ 2 + M.charpoly.coeff 2 * c + 1) • (1 : Mat) := by
    apply Matrix.ext
    intro i j
    have hij := congrArg (fun A : Mat => A i j) h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at hij ⊢
    linear_combination -hij
  refine ⟨(c * Matrix.trace M + star (Matrix.trace M))⁻¹ *
    (c ^ 2 + M.charpoly.coeff 2 * c + 1), ?_⟩
  have he' := congrArg (fun A : Mat =>
    (c * Matrix.trace M + star (Matrix.trace M))⁻¹ • A) he
  simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using he'

private theorem special_det (g : (form 4).specialSubgroup) : g.val.val.det = 1 := by
  have hd := ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.2
  have h := congrArg (fun d : Fˣ => (d : F)) hd
  rw [GeneralLinearGroup.val_det_apply, Units.val_one] at h
  exact h

/-- A lift of a projective involution squares to one of the full four scalar roots. -/
public theorem square_scalar (g : (form 4).specialSubgroup) (h : (project 4 g) ^ 2 = 1) :
    ∃ u : FiniteField.Nineˣ, u ^ 4 = 1 ∧
      g.val.val ^ 2 = (u : FiniteField.Nine) •
        (1 : Matrix (Fin 4) (Fin 4) FiniteField.Nine) := by
  have hk : g ^ 2 ∈ (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project
      F (form 4)).ker := by
    change project 4 (g ^ 2) = 1
    rwa [map_pow]
  obtain ⟨u, hu, he⟩ := (IsotropicStabilizers.mem_project_kernel_iff (form 4) (g ^ 2)).mp hk
  refine ⟨u, hu, ?_⟩
  have he' := congrArg (fun a : GL (Fin 4) F => a.val) he
  simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Subgroup.coe_pow,
    Units.val_pow_eq_pow_val, Matrix.smul_one_eq_diagonal] using he'.symm

private theorem project_eq_one_of_scalar (g : (form 4).specialSubgroup) (a : F)
    (ha : g.val.val = a • (1 : Mat)) : project 4 g = 1 := by
  have ha0 : a ≠ 0 := by
    intro he
    have hd := special_det g
    rw [ha, he, zero_smul, Matrix.det_zero] at hd
    exact zero_ne_one hd
  let u : Fˣ := Units.mk0 a ha0
  have hu : GeneralLinearGroup.scalar (Fin 4) u = g.val := by
    apply Units.ext
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal, u, Units.val_mk0] using ha.symm
  apply Subtype.ext
  change ProjGenLinGroup.mk g.val = 1
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, hu⟩

/-- Every lift of a nonidentity projective involution in PSU₄(3) has trace zero. -/
public theorem trace_eq_zero_of_projective_involution (g : (form 4).specialSubgroup)
    (hne : project 4 g ≠ 1) (hsq : (project 4 g) ^ 2 = 1) :
    Matrix.trace g.val.val = 0 := by
  by_contra ht
  obtain ⟨u, _, hu⟩ := square_scalar g hsq
  have hunit := ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.1
  change g.val.val.conjTranspose * 1 * g.val.val = 1 at hunit
  rw [mul_one] at hunit
  obtain ⟨a, ha⟩ := scalar_of_square_scalar_of_trace_ne_zero g.val.val
    (special_det g) hunit u.val u.ne_zero hu ht
  exact hne (project_eq_one_of_scalar g a ha)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer
