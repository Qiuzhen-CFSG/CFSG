module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.ScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Cocycle

/-!
# Involutory unitary graph twists in dimension five

Squaring unitary conjugation followed by Hermitian conjugation shows that
the matrix norm projectively centralizes PSU₅(4). The projective centralizer
calculation makes the norm scalar. This scalar is fixed by conjugation and
has square one, so it equals one in characteristic two. Matrix descent then
constructs a unitary change of coordinates giving literal graph conjugacy.

Source: F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
The norm reduction adapts the dimension-three proof in
SU3/ProjectiveOuterInvolutions/Descent/Reduction.lean. The input here is an
actual unitary graph-twist formula; no semilinear representation theorem for
an abstract automorphism, or flag compatibility, is asserted.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent
variable {E : Type*} [Field E] (J : HermitianForm 5 E)

/-- The square-one twist makes its matrix norm centralize the actual PSU image. -/
theorem projective_norm_commutes_of_twist_sq (hJ : J.form = 1) (u : J.unitarySubgroup)
    (hu : (unitaryConj J u * GraphFixed.projectiveAut J hJ)^2 = 1)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Commute (Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val)) b.val := by
  have h := congrArg (fun a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => (a b).val) hu
  change (unitaryConj J u (GraphFixed.projectiveAut J hJ
    (unitaryConj J u (GraphFixed.projectiveAut J hJ b)))).val = b.val at h
  rw [unitaryConj_apply_val, projectiveAut_apply_val,
    unitaryConj_apply_val, map_mul, map_mul, map_inv] at h
  rw [← projectiveAut_apply_val J hJ,
    GraphFixed.projectiveAut_involutive, Matrix.ProjGenLinGroup.map_mk] at h
  change _ * _ = _ * _
  apply (mul_inv_eq_iff_eq_mul).mp
  simpa [map_mul, mul_assoc] using h

private theorem map_conj_map_conj (A : GL (Fin 5) E) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom
      (Matrix.GeneralLinearGroup.map J.conj.toRingHom A) = A := by
  apply Units.ext
  ext i j
  exact J.conj_involutive _

private theorem map_conj_mem_unitary (hJ : J.form.map J.conj = J.form)
    (u : J.unitarySubgroup) :
    Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.val.map J.conj) * J.form *
    (u.val.val.map J.conj) = J.form
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) E => A.map J.conj)
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
  have hN : N ∈ Subgroup.center (GL (Fin 5) E) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hu
  have hNfix : Matrix.GeneralLinearGroup.map J.conj.toRingHom N = N := by
    apply mul_left_cancel (a := u.val)
    have hc := Subgroup.mem_center_iff.mp hN u.val
    simpa only [N, map_mul, map_conj_map_conj, mul_assoc] using hc.symm
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hN
  have hcfix : J.conj c = c := by
    have h := congrArg (fun A : GL (Fin 5) E => A.val 0 0) hNfix
    change J.conj (N.val 0 0) = N.val 0 0 at h
    simpa [← hc, Matrix.scalar_apply] using h
  have hNu : N ∈ J.unitarySubgroup :=
    J.unitarySubgroup.mul_mem u.property (map_conj_mem_unitary J hJ u)
  have hunitary := (J.mem_unitarySubgroup_iff N).mp hNu
  have hadj : J.conjTranspose (Matrix.scalar (Fin 5) c) = Matrix.scalar (Fin 5) c := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hcfix]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [← hc, hadj] at hunitary
  obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have hentry := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M 0 j) hunitary
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
/-- A represented involution has a genuine matrix cocycle, despite the
nontrivial projective scalar kernel. -/
theorem unitary_cocycle_of_twist_sq [Finite E] [CharP E 2]
    (hJ : J.form = 1) (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card E=16)
    (u : J.unitarySubgroup)
    (hu : (unitaryConj J u * GraphFixed.projectiveAut J hJ)^2 = 1) :
    u.val * Matrix.GeneralLinearGroup.map J.conj.toRingHom u.val = 1 := by
  apply norm_eq_one_of_projective_norm_eq_one J (by rw [hJ]; simp) u
  apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
  exact projective_centralizer_scalar J hJ hconj hcard _
    (projective_norm_commutes_of_twist_sq J hJ u hu)

/-- Every involution represented by a unitary graph twist is conjugate to
the specified graph action, through an explicit unitary change of basis. -/
theorem conjugate_graph_of_twist_sq [Finite E] [CharP E 2]
    (hJ : J.form = 1) (hσ : J.conj ≠ 1)
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card E=16)
    (u : J.unitarySubgroup)
    (hu : (unitaryConj J u * GraphFixed.projectiveAut J hJ)^2 = 1) :
    ∃ v : J.unitarySubgroup,
      unitaryConj J u * GraphFixed.projectiveAut J hJ =
        unitaryConj J v * GraphFixed.projectiveAut J hJ * (unitaryConj J v)⁻¹ := by
  obtain ⟨v,hv⟩ := unitary_cocycle_coboundary J hJ hσ u
    (unitary_cocycle_of_twist_sq J hJ hconj hcard u hu)
  exact ⟨v,conjugate_graph_of_coboundary J hJ u v hv⟩

end Theory.SpecificGroups.UnitaryFive.Descent

