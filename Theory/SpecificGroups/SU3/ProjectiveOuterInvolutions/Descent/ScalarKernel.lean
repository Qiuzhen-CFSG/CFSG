module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.CharP.Two

/-!
# The projective centralizer of the binary special unitary image

An invertible matrix projectively centralizing PSU₃ commutes with each
trace-one unipotent representative: taking traces of a projective conjugacy
relation forces its scalar multiplier to be one. Commuting with the upper
and lower central roots forces the matrix to be diagonal with equal outer
entries. A root with first parameter one then equates the middle entry.

The latter root exists because a nontrivial involution has a trace-one
field element, explicitly `t / (t + conj(t))` in characteristic two.
The upper roots use the concrete Huppert II.10.12 matrix interface.
This supplies the scalar-kernel step for GLS, Volume 3,
Proposition 4.9.2(b2,g), specialized to twisted A₂ in characteristic two.
-/

open BenderSuzuki.MatrixGroups Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E]

private theorem commute_of_projective_commute_of_trace_ne_zero
    (A X : GL (Fin 3) E) (hX : X.val.trace ≠ 0)
    (h : Commute (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk X)) : Commute A X := by
  have hp : ProjGenLinGroup.mk (A * X * A⁻¹) = ProjGenLinGroup.mk X := by
    simpa only [map_mul, map_inv] using (mul_inv_eq_iff_eq_mul).mpr h.eq
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have hm : ((A * X * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * X.val * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj] at ht
  have hc1 : c = 1 := Units.ext (mul_right_cancel₀ hX (ht.trans (one_mul _).symm))
  rw [hc1, map_one, mul_one] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc : A * X = X * A)

variable (J : HermitianForm 3 E) [CharP E 2]
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
private def upperRoot : J.specialSubgroup := by
  exact BenderSuzuki.External.hermitianUnipotentSU J hJ
    ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩

private def lowerRoot : J.specialSubgroup := by
  let L : Matrix (Fin 3) (Fin 3) E := !![1, 0, 0; 0, 1, 0; 1, 0, 1]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero L (by simp [L, det_fin_three]), ?_⟩
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  · apply Units.ext
    change L.det = 1
    simp [L, det_fin_three]

private theorem exists_trace_one (hconj : ∃ t : E, J.conj t ≠ t) :
    ∃ b : E, b + J.conj b = 1 := by
  obtain ⟨t, ht⟩ := hconj
  have hden : t + J.conj t ≠ 0 := by
    intro h
    apply ht
    calc
      J.conj t = t + (t + J.conj t) := by simp [← add_assoc, CharTwo.add_self_eq_zero]
      _ = t := by rw [h, add_zero]
  refine ⟨t / (t + J.conj t), ?_⟩
  rw [map_div₀, map_add, J.conj_involutive, add_comm (J.conj t) t,
    ← add_div, div_self hden]

include hJ in
/-- A matrix projectively centralizing the actual PSU₃ image is scalar. -/
public theorem projective_centralizer_scalar
    (hconj : ∃ t : E, J.conj t ≠ t)
    (A : GL (Fin 3) E)
    (hA : ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
      Commute (ProjGenLinGroup.mk A) b.val) :
    A ∈ Subgroup.center (GL (Fin 3) E) := by
  obtain ⟨b, hb⟩ := exists_trace_one J hconj
  let R := BenderSuzuki.External.hermitianUnipotentSU J hJ
    ⟨(1, b), by simp [hb, CharTwo.add_self_eq_zero]⟩
  have hcomm (X : J.specialSubgroup) (htr : X.val.val.trace ≠ 0) :
      A.val * X.val.val = X.val.val * A.val :=
    congrArg Units.val
      (commute_of_projective_commute_of_trace_ne_zero A X.val htr
        (by simpa only [specialToProjective_apply_val] using hA (J.specialToProjective X))).eq
  have hU := hcomm (upperRoot J hJ) (by
    simp [upperRoot, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix,
      Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hL := hcomm (lowerRoot J hJ) (by
    simp [lowerRoot, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hR := hcomm R (by
    simp [R, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix,
      Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  have hUmat : (upperRoot J hJ).val.val = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
    simp [upperRoot, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix]
  rw [hUmat] at hU
  change A.val * !![1, 0, 0; 0, 1, 0; 1, 0, 1] =
    !![1, 0, 0; 0, 1, 0; 1, 0, 1] * A.val at hL
  have hRmat : R.val.val = !![1, 1, b; 0, 1, 1; 0, 0, 1] := by
    simp [R, BenderSuzuki.External.hermitianUnipotentSU,
      BenderSuzuki.External.hermitianUnipotentGL, BenderSuzuki.External.hermitianUnipotentMatrix,
      CharTwo.neg_eq]
  rw [hRmat] at hR
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hU
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hU
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hU
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) hU
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hL
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 1) hL
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 0) hL
  have hmid := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) hR
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h20 h21 hdiag h10 h02 h01 h12 hmid
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨A.val 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  all_goals grind

end BenderSuzuki.MatrixGroups.HermitianForm

