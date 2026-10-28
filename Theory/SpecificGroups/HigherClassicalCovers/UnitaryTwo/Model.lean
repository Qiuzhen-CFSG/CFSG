module

public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The concrete unitary-four model over the field of order four

The scalar kernel of SU₄(2) → PSU₄(2) is trivial: the determinant and
Hermitian conditions give scalar orders dividing four and three. Thus the
literal projective map is an isomorphism. Orthonormal bases and an actual
coefficient-field isomorphism then identify every allowed Hermitian form
with the identity form over the existing computable field `GoldenFour`.
The comparison retains the commuting square of projective maps.

These are the arbitrary-form reductions for the U₄(2) row of
Aschbacher–Smith I.1.4(1), printed p.408, `refs/quasithin.pdf`.
This module does not identify the concrete group with PSp₄(3).
-/

public section
noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo

/-- The identity Hermitian form with square Frobenius on the concrete field. -/
@[expose] def standardForm : HermitianForm 4 Atlas.Algebra.GoldenFour where
  conj := starRingAut
  conj_involutive := fun x => star_star x
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

abbrev StandardSU := standardForm.specialSubgroup
abbrev StandardPSU := ProjectiveSpecialUnitaryMatrixGroup standardForm

theorem standard_field_card : Nat.card Atlas.Algebra.GoldenFour = 4 := by
  rw [Nat.card_eq_fintype_card, Atlas.Algebra.goldenFour_card]

theorem standard_conj (x : Atlas.Algebra.GoldenFour) :
    standardForm.conj x = x ^ 2 := by
  revert x
  decide +kernel

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 4 F)

theorem fixed_card (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) :
    Nat.card {x : F // J.conj x = x} = 2 := by
  simpa only [pow_one] using
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 (by decide)
      (by simpa using hF) (by simpa using hc)

/-- The literal projective map has trivial scalar kernel in degree four over F₄. -/
theorem project_ker_eq_bot (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) :
    (project J).ker = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  simpa using card_project_kernel J hc (by simpa using hF)

/-- SU₄(2) is identified with its actual image in PGL by projectivization. -/
@[expose] def specialProjectiveEquiv (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (project J)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (project_ker_eq_bot J hF hc), project_surjective J⟩

@[simp] theorem specialProjectiveEquiv_apply
    (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) (x : J.specialSubgroup) :
    specialProjectiveEquiv J hF hc x = project J x := rfl

/-- Transport the actual determinant-one isometry group to the concrete form. -/
def specialEquivStandard (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) :
    J.specialSubgroup ≃* StandardSU :=
  Classical.choice (HermitianForm.nonempty_specialEquiv_of_card J standardForm 2
    (by simpa using hF) (fixed_card J hF hc)
    (by simpa using standard_field_card)
    (fixed_card standardForm standard_field_card standard_conj))

/-- Transport the actual projective group, for every field and Hermitian form. -/
def projectiveEquivStandard (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* StandardPSU :=
  (specialProjectiveEquiv J hF hc).symm.trans
    ((specialEquivStandard J hF hc).trans
      (specialProjectiveEquiv standardForm standard_field_card standard_conj))

/-- The special and projective comparisons commute with the literal projections. -/
theorem projectiveEquivStandard_project
    (hF : Nat.card F = 4) (hc : ∀ x, J.conj x = x ^ 2) (x : J.specialSubgroup) :
    projectiveEquivStandard J hF hc (project J x) =
      project standardForm (specialEquivStandard J hF hc x) := by
  change specialProjectiveEquiv standardForm standard_field_card standard_conj
    (specialEquivStandard J hF hc ((specialProjectiveEquiv J hF hc).symm
      (specialProjectiveEquiv J hF hc x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl


end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
