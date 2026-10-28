module
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.Model
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.ProjectiveOmega
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Hermitian congruences over an arbitrary involutive field automorphism

The literal fixed field of `σ` is the coefficient field. Hermitian matrices
have coordinates `(a,b,z)` and determinant `a*b - z*σ(z)`. The actual SL₂
congruence action preserves this quadratic form and its negative, and thus
defines a homomorphism into the full quadratic-isometry group.

We use negative determinant for comparison with the chosen minus form:
its anisotropic summand is the norm, and negating one hyperbolic coordinate
restores the positive hyperbolic product. This keeps the quadratic transport
valid in odd characteristic. No image equality or kernel assertion is built
into these definitions.

This extends the characteristic-free identities in
`OrthogonalFourMinusFirstCohomology.Model` and the coordinate construction of
its binary `FiniteModel.Basic`. The concrete consumers are the orthogonal
homomorphism below and the projective comparison's image and transport proofs.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39, and I.1.6(3),
printed p.408 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

/-- The literal fixed subfield of the stored conjugation. -/
def fixedField : Subfield E := FixedBy.subfield E σ

/-- Conjugation as an automorphism over its fixed field. -/
def conjugationAlg : E ≃ₐ[fixedField σ] E :=
  AlgEquiv.ofRingEquiv (f := σ) (fun x => x.property)

/-- The Hermitian subspace of two-by-two matrices. -/
abbrev Space : Type u :=
  (hermitian (conjugationAlg σ) hσ).toSubmodule

/-- The actual SL₂ action on the Hermitian matrix space. -/
def action :
    Representation (fixedField σ) (Matrix.SpecialLinearGroup (Fin 2) E) (Space σ hσ) :=
  hermitianAction (conjugationAlg σ) hσ

lemma entry_fixed (X : Space σ hσ) (i : Fin 2) :
    σ (X.val i i) = X.val i i := congrFun (congrFun X.property i) i

lemma entry_conjugate (X : Space σ hσ) (i j : Fin 2) :
    σ (X.val j i) = X.val i j := congrFun (congrFun X.property i) j

/-- Two fixed diagonal entries and one arbitrary upper-right entry. -/
def coordinates :
    Space σ hσ ≃ₗ[fixedField σ] ((fixedField σ × fixedField σ) × E) where
  toFun X := ((⟨X.val 0 0, entry_fixed σ hσ X 0⟩, ⟨X.val 1 1, entry_fixed σ hσ X 1⟩), X.val 0 1)
  invFun v := ⟨!![v.1.1.val, v.2; σ v.2, v.1.2.val], by
    ext i j
    fin_cases i <;> fin_cases j
    · exact v.1.1.property
    · exact hσ v.2
    · rfl
    · exact v.1.2.property⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    exact entry_conjugate σ hσ X 1 0
  right_inv v := by rfl
  map_add' X Y := by rfl
  map_smul' c X := by rfl

/-- Determinant with values in the actual fixed field. -/
def determinant (X : Space σ hσ) : fixedField σ :=
  ⟨X.val.det, det_fixed (conjugationAlg σ) hσ X⟩

lemma determinant_smul (c : fixedField σ) (X : Space σ hσ) :
    determinant σ hσ (c • X) = (c * c) • determinant σ hσ X := by
  apply Subtype.ext
  simp [determinant, Subfield.smul_def, smul_eq_mul, pow_two]

/-- The determinant quadratic form, including in characteristic two. -/
def form : QuadraticForm (fixedField σ) (Space σ hσ) :=
  QuadraticMap.ofPolar (determinant σ hσ) (determinant_smul σ hσ)
    (by
      intro X Y Z
      apply Subtype.ext
      simp [QuadraticMap.polar, determinant, Matrix.det_fin_two]
      ring)
    (by
      intro c X Y
      apply Subtype.ext
      simp [QuadraticMap.polar, determinant, Matrix.det_fin_two, Matrix.smul_apply,
        Subfield.smul_def, smul_eq_mul]
      ring)

@[simp] lemma form_apply (X : Space σ hσ) :
    form σ hσ X = determinant σ hσ X := rfl

lemma form_preserved (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (X : Space σ hσ) : form σ hσ (action σ hσ A X) = form σ hσ X := by
  apply Subtype.ext
  exact det_hermitianAction (conjugationAlg σ) hσ A X

/-- The norm into the actual fixed subfield. -/
def norm (z : E) : fixedField σ :=
  ⟨z * σ z, by
    change σ (z * σ z) = z * σ z
    rw [map_mul, hσ]
    exact mul_comm _ _⟩

@[simp] lemma norm_eq_zero_iff (z : E) :
    norm σ hσ z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have he : z * σ z = 0 := congrArg Subtype.val h
    rcases mul_eq_zero.mp he with h | h
    · exact h
    · exact σ.injective (h.trans (map_zero _).symm)
  · rintro rfl
    apply Subtype.ext
    exact zero_mul _

lemma form_coordinates (v : (fixedField σ × fixedField σ) × E) :
    form σ hσ ((coordinates σ hσ).symm v) = v.1.1 * v.1.2 - norm σ hσ v.2 := by
  apply Subtype.ext
  change ( !![v.1.1.val, v.2; σ v.2, v.1.2.val] : Mat E).det = _
  rw [Matrix.det_fin_two]
  rfl

@[simp] lemma coe_form (X : Space σ hσ) :
    (form σ hσ X : E) = X.val.det := rfl

@[simp] lemma coordinates_symm_val
    (v : (fixedField σ × fixedField σ) × E) :
    ((coordinates σ hσ).symm v).val = !![v.1.1.val, v.2; σ v.2, v.1.2.val] := rfl

lemma action_apply (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (X : Space σ hσ) : (action σ hσ A X).val = A.val * X.val * adjoint σ A.val := rfl


/-- Negative determinant; the sign makes its anisotropic summand the norm. -/
def minusForm : QuadraticForm (fixedField σ) (Space σ hσ) := -form σ hσ

@[simp] theorem minusForm_apply (X : Space σ hσ) :
    minusForm σ hσ X = -determinant σ hσ X := rfl

theorem minusForm_coordinates (v : (fixedField σ × fixedField σ) × E) :
    minusForm σ hσ ((coordinates σ hσ).symm v) = norm σ hσ v.2 - v.1.1 * v.1.2 := by
  change -(form σ hσ ((coordinates σ hσ).symm v)) = _
  rw [form_coordinates]
  ring

theorem minusForm_preserved (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (X : Space σ hσ) : minusForm σ hσ (action σ hσ A X) = minusForm σ hσ X := by
  change -(form σ hσ (action σ hσ A X)) = -(form σ hσ X)
  rw [form_preserved]

/-- The same congruence action valued in linear equivalences. -/
def linearActionHom : Matrix.SpecialLinearGroup (Fin 2) E →*
    (Space σ hσ ≃ₗ[fixedField σ] Space σ hσ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (fixedField σ) (Space σ hσ)).toMonoidHom.comp
    (action σ hσ).asGroupHom

@[simp] theorem linearActionHom_apply (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (X : Space σ hσ) : linearActionHom σ hσ A X = action σ hσ A X := rfl

/-- The actual SL₂ congruences inside the full negative-determinant isometry group. -/
def orthogonalAction : Matrix.SpecialLinearGroup (Fin 2) E →*
    Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ) where
  toFun A := ⟨linearActionHom σ hσ A,
    (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (minusForm_preserved σ hσ A)⟩
  map_one' := Subtype.ext (map_one (linearActionHom σ hσ))
  map_mul' A B := Subtype.ext (map_mul (linearActionHom σ hσ) A B)

@[simp] theorem orthogonalAction_apply (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (X : Space σ hσ) : (orthogonalAction σ hσ A).val X = action σ hσ A X := rfl

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
