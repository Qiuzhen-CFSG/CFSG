module

public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction

/-!
# Unitary conjugation on the projective special unitary image

A unitary matrix normalizes the determinant-one subgroup and therefore acts on
its actual image in PGL. The formulas below retain this image map throughout;
no identification with an abstract quotient or group-family label is needed.

The final lemma converts a projective matrix coboundary into conjugacy of the
specified entrywise automorphism. This is the compatibility step in the matrix
approach to GLS, Volume 4, Chapter 4, Lemma 3.4(a,c); the missing automorphism
normal form and descent theorem are separate mathematical inputs. Compare GLS,
Volume 3, Theorem 2.5.12, the unitary matrix description in Section 2.7, and
Proposition 4.9.2(b2,g).
-/

open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Conjugation by a unitary matrix preserves the special unitary subgroup. -/
public def specialUnitaryConj (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    J.specialSubgroup :=
  ⟨u.val * x.val * u.val⁻¹, by
    refine ⟨J.unitarySubgroup.mul_mem
      (J.unitarySubgroup.mul_mem u.property x.property.1)
      (J.unitarySubgroup.inv_mem u.property), ?_⟩
    change Matrix.GeneralLinearGroup.det (u.val * x.val * u.val⁻¹) = 1
    have hx : Matrix.GeneralLinearGroup.det x.val = 1 := x.property.2
    simp [map_mul, hx]⟩

/-- The matrix underlying conjugation inside the special unitary group. -/
public theorem specialUnitaryConj_val (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    (J.specialUnitaryConj u x).val = u.val * x.val * u.val⁻¹ := by rfl

private theorem projective_conj_mem (u : J.unitarySubgroup)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Matrix.ProjGenLinGroup.mk u.val * b.val * (Matrix.ProjGenLinGroup.mk u.val)⁻¹ ∈
      J.specialSubgroup.map Matrix.ProjGenLinGroup.mk := by
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  refine ⟨(specialUnitaryConj J u x).val, (specialUnitaryConj J u x).property, ?_⟩
  simp [specialUnitaryConj, map_mul]

/-- The automorphism induced on the exact projective image by a unitary matrix. -/
public def unitaryConj (u : J.unitarySubgroup) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun b := ⟨Matrix.ProjGenLinGroup.mk u.val * b.val *
    (Matrix.ProjGenLinGroup.mk u.val)⁻¹, projective_conj_mem J u b⟩
  invFun b := ⟨Matrix.ProjGenLinGroup.mk (u⁻¹).val * b.val *
    (Matrix.ProjGenLinGroup.mk (u⁻¹).val)⁻¹, projective_conj_mem J u⁻¹ b⟩
  left_inv b := by apply Subtype.ext; simp [mul_assoc]
  right_inv b := by apply Subtype.ext; simp [mul_assoc]
  map_mul' b c := by apply Subtype.ext; simp [mul_assoc]

/-- Compatibility of unitary conjugation with special unitary representatives. -/
public theorem unitaryConj_specialToProjective (u : J.unitarySubgroup) (x : J.specialSubgroup) :
    unitaryConj J u (J.specialToProjective x) =
      J.specialToProjective (specialUnitaryConj J u x) := by
  apply Subtype.ext
  simp [unitaryConj, specialUnitaryConj, map_mul]

/-- The ambient PGL formula for the induced automorphism. -/
public theorem unitaryConj_apply_val (u : J.unitarySubgroup)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (unitaryConj J u b).val = Matrix.ProjGenLinGroup.mk u.val * b.val *
      (Matrix.ProjGenLinGroup.mk u.val)⁻¹ := by rfl

/-- A projective coboundary for entrywise conjugation gives an actual conjugating
automorphism of the projective special unitary group. -/
public theorem congr_unitaryConj_of_projective_coboundary
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (u v : J.unitarySubgroup)
    (huv : Matrix.ProjGenLinGroup.mk u.val =
      Matrix.ProjGenLinGroup.mk
        (v.val * (Matrix.GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹)) :
    MulAut.congr (unitaryConj J v) γ = unitaryConj J u * γ := by
  apply MulEquiv.ext
  intro b
  obtain ⟨b, rfl⟩ := (unitaryConj J v).surjective b
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
  change unitaryConj J v (γ ((unitaryConj J v).symm
      (unitaryConj J v (J.specialToProjective x)))) =
    unitaryConj J u (γ (unitaryConj J v (J.specialToProjective x)))
  rw [MulEquiv.symm_apply_apply, unitaryConj_specialToProjective]
  obtain ⟨y, hy, hγx⟩ := hγ x
  obtain ⟨z, hz, hγvx⟩ := hγ (specialUnitaryConj J v x)
  rw [hγx, hγvx]
  have hy' : y.val = Matrix.GeneralLinearGroup.map J.conj.toRingHom x.val :=
    Units.ext hy
  have hz' : z.val = Matrix.GeneralLinearGroup.map J.conj.toRingHom
      (v.val * x.val * v.val⁻¹) := Units.ext hz
  apply Subtype.ext
  simp only [unitaryConj_apply_val, specialToProjective_apply_val, hy', hz',
    huv, map_mul, map_inv]
  simp [mul_assoc]

end BenderSuzuki.MatrixGroups.HermitianForm
