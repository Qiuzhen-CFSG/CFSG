module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.GraphFixed

/-!
# Unitary changes of coordinates on the actual PSU₅ carrier

Conjugation by a unitary matrix normalizes SU₅ and acts on its image in
PGL. A unitary coboundary for Hermitian conjugation therefore gives a
literal conjugated-graph equation on that projective carrier. No scalar
projection is assumed injective, and the conjugating automorphism need
not be an element of a chosen extension.

This is the compatibility calculation for the matrix descent in F.4.29(2),
printed p.289 of refs/quasithin.pdf. Compare the dimension-three construction
in SU3/ProjectiveOuterInvolutions/UnitaryConjugation.lean.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent
variable {E : Type*} [Field E] (J : HermitianForm 5 E)

/-- Conjugation by a unitary matrix preserves the special unitary subgroup. -/
def specialUnitaryConj (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    J.specialSubgroup :=
  ⟨u.val * x.val * u.val⁻¹, by
    refine ⟨J.unitarySubgroup.mul_mem
      (J.unitarySubgroup.mul_mem u.property x.property.1)
      (J.unitarySubgroup.inv_mem u.property), ?_⟩
    change Matrix.GeneralLinearGroup.det (u.val * x.val * u.val⁻¹) = 1
    have hx : Matrix.GeneralLinearGroup.det x.val = 1 := x.property.2
    simp [map_mul, hx]⟩

/-- The matrix underlying conjugation inside the special unitary group. -/
theorem specialUnitaryConj_val (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    (specialUnitaryConj J u x).val = u.val * x.val * u.val⁻¹ := by rfl

private theorem projective_conj_mem (u : J.unitarySubgroup)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Matrix.ProjGenLinGroup.mk u.val * b.val * (Matrix.ProjGenLinGroup.mk u.val)⁻¹ ∈
      J.specialSubgroup.map Matrix.ProjGenLinGroup.mk := by
  obtain ⟨x, rfl⟩ := project_surjective J b
  refine ⟨(specialUnitaryConj J u x).val, (specialUnitaryConj J u x).property, ?_⟩
  change Matrix.ProjGenLinGroup.mk (u.val * x.val * u.val⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

/-- The automorphism induced on the exact projective image by a unitary matrix. -/
def unitaryConj (u : J.unitarySubgroup) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun b := ⟨Matrix.ProjGenLinGroup.mk u.val * b.val *
    (Matrix.ProjGenLinGroup.mk u.val)⁻¹, projective_conj_mem J u b⟩
  invFun b := ⟨Matrix.ProjGenLinGroup.mk (u⁻¹).val * b.val *
    (Matrix.ProjGenLinGroup.mk (u⁻¹).val)⁻¹, projective_conj_mem J u⁻¹ b⟩
  left_inv b := by apply Subtype.ext; simp [mul_assoc]
  right_inv b := by apply Subtype.ext; simp [mul_assoc]
  map_mul' b c := by apply Subtype.ext; simp [mul_assoc]

/-- Compatibility of unitary conjugation with special unitary representatives. -/
theorem unitaryConj_project (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    unitaryConj J u (project J x) =
      project J (specialUnitaryConj J u x) := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk u.val * Matrix.ProjGenLinGroup.mk x.val *
    (Matrix.ProjGenLinGroup.mk u.val)⁻¹ =
      Matrix.ProjGenLinGroup.mk (u.val * x.val * u.val⁻¹)
  simp only [map_mul,map_inv]

/-- The ambient PGL formula for the induced automorphism. -/
theorem unitaryConj_apply_val (u : J.unitarySubgroup)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (unitaryConj J u b).val = Matrix.ProjGenLinGroup.mk u.val * b.val *
      (Matrix.ProjGenLinGroup.mk u.val)⁻¹ := by rfl

/-- The graph automorphism acts entrywise on the literal PGL image. -/
theorem projectiveAut_apply_val (hJ : J.form = 1)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (GraphFixed.projectiveAut J hJ b).val =
      Matrix.ProjGenLinGroup.map J.conj.toRingHom b.val := by
  obtain ⟨x,rfl⟩ := project_surjective J b
  rw [GraphFixed.projectiveAut_project]
  rfl

/-- A unitary coboundary gives conjugacy to the specified graph action on PSU₅. -/
theorem conjugate_graph_of_coboundary (hJ : J.form = 1) (u v : J.unitarySubgroup)
    (huv : u.val = v.val * (Matrix.GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹) :
    unitaryConj J u * GraphFixed.projectiveAut J hJ =
      unitaryConj J v * GraphFixed.projectiveAut J hJ * (unitaryConj J v)⁻¹ := by
  apply MulEquiv.ext
  intro b
  obtain ⟨b,rfl⟩ := (unitaryConj J v).surjective b
  change unitaryConj J u (GraphFixed.projectiveAut J hJ (unitaryConj J v b)) =
    unitaryConj J v (GraphFixed.projectiveAut J hJ
      ((unitaryConj J v).symm (unitaryConj J v b)))
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  simp only [unitaryConj_apply_val,projectiveAut_apply_val,map_mul,map_inv,
    Matrix.ProjGenLinGroup.map_mk,huv]
  simp [mul_assoc]

end Theory.SpecificGroups.UnitaryFive.Descent
