module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# From an involutory projective twist to a matrix cocycle

The square of unitary conjugation followed by entrywise conjugation is
conjugation by the projective class of `u * conj(u)`. Thus the square-one
hypothesis puts this class in the centralizer of the actual PSU image.

If this class is trivial, its matrix representative is scalar. Centrality
makes that scalar fixed by the field involution. The unitary equation then
makes its square one, hence it is one in characteristic two. This explicitly
removes the scalar ambiguity before applying matrix descent.

These are reductions for the twisted A₂ case of GLS, Volume 3,
Proposition 4.9.2(b2,g), used in Volume 4, Chapter 4, Lemma 3.4(a,c).
The projective centralizer calculation and the unitary cocycle theorem are
separate inputs; neither is assumed to follow from these reductions.
-/

open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Entrywise action on the ambient projective matrix group. -/
public theorem IsEntrywiseConjugation.apply_val
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (γ b).val = Matrix.ProjGenLinGroup.map J.conj.toRingHom b.val := by
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  obtain ⟨y, hy, hγx⟩ := hγ x
  rw [hγx]
  simp only [specialToProjective_apply_val, Matrix.ProjGenLinGroup.map_mk]
  have hy' : y.val = Matrix.GeneralLinearGroup.map J.conj.toRingHom x.val := Units.ext hy
  exact congrArg Matrix.ProjGenLinGroup.mk hy'

/-- The square-one twist hypothesis makes the projective matrix norm centralize PSU₃. -/
public theorem projective_norm_commutes_of_twist_sq
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u : J.unitarySubgroup)
    (hu : (J.unitaryConj u * γ)^2 = 1)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Commute (Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val)) b.val := by
  have hγγ : γ (γ b) = b := DFunLike.congr_fun hγ.sq_eq_one b
  have h := congrArg (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (a b).val) hu
  change (J.unitaryConj u (γ (J.unitaryConj u (γ b)))).val = b.val at h
  rw [unitaryConj_apply_val, IsEntrywiseConjugation.apply_val J hγ,
    unitaryConj_apply_val, map_mul, map_mul, map_inv] at h
  rw [← IsEntrywiseConjugation.apply_val J hγ, hγγ, Matrix.ProjGenLinGroup.map_mk] at h
  change _ * _ = _ * _
  apply (mul_inv_eq_iff_eq_mul).mp
  simpa [map_mul, mul_assoc] using h

private theorem map_conj_map_conj (A : GL (Fin 3) E) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom
      (Matrix.GeneralLinearGroup.map J.conj.toRingHom A) = A := by
  apply Units.ext
  ext i j
  exact J.conj_involutive _

private theorem map_conj_mem_unitary (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val ∈ J.unitarySubgroup := by
  rw [mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map J.conj) * J.form *
    (u.val.val.map J.conj) = J.form
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map J.conj)
    ((J.mem_unitarySubgroup_iff u.val).mp u.property)
  have ha : (J.conjTranspose u.val.val).map J.conj =
      J.conjTranspose (u.val.val.map J.conj) := by
    ext i j
    rfl
  simpa only [RingEquiv.mapMatrix_apply, Matrix.map_mul,
    ha, hJ] using h

/-- In characteristic two a projectively trivial unitary matrix norm equals one. -/
public theorem norm_eq_one_of_projective_norm_eq_one [CharP E 2]
    (hJ : J.form.map J.conj = J.form) (u : J.unitarySubgroup)
    (hu : Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val) = 1) :
    u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
  let N := u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val
  have hN : N ∈ Subgroup.center (GL (Fin 3) E) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hu
  have hNfix : Matrix.GeneralLinearGroup.map J.conj.toRingHom N = N := by
    apply mul_left_cancel (a := u.val)
    have hc := Subgroup.mem_center_iff.mp hN u.val
    simpa only [N, map_mul, map_conj_map_conj, mul_assoc] using hc.symm
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hN
  have hcfix : J.conj c = c := by
    have h := congrArg (fun A : GL (Fin 3) E => A.val 0 0) hNfix
    change J.conj (N.val 0 0) = N.val 0 0 at h
    simpa [← hc, Matrix.scalar_apply] using h
  have hNu : N ∈ J.unitarySubgroup :=
    J.unitarySubgroup.mul_mem u.property (map_conj_mem_unitary J hJ u)
  have hunitary := (J.mem_unitarySubgroup_iff N).mp hNu
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) c := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hcfix]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [← hc, hadj] at hunitary
  obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 j) hunitary
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hcsq : c * c = 1 := by
    apply mul_right_cancel₀ hj
    calc
      (c * c) * J.form 0 j = c * J.form 0 j * c := by ring
      _ = J.form 0 j := hentry
      _ = 1 * J.form 0 j := (one_mul _).symm
  have hc1 : c = 1 := by
    apply frobenius_inj E 2
    change c ^ 2 = 1 ^ 2
    simpa only [pow_two, one_mul] using hcsq
  change N = 1
  apply Units.ext
  rw [← hc, hc1]
  simp
end BenderSuzuki.MatrixGroups.HermitianForm

