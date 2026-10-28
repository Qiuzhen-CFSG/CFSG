module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.Basic
/-!
# Norm-plane rotations and the SL₂ image

Multiplication by a norm-one element on the off-diagonal coordinate is an
isometry fixing both diagonal vectors. These rotations commute, and
conjugation inverts them. Their squares are determinant-one diagonal
congruences. Each rotation itself is congruence by diag(u,1), so conjugating
SL₂ by that matrix proves that it normalizes the literal SL₂ image.

These relations account for the determinant square classes in odd
characteristic: no norm-one square root is chosen. The pair-stabilizer and
full-orthogonal-quotient arguments consume the explicit actions below.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39
(`refs/quasithin.pdf`).
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

private lemma norm_one_ne_zero (u : E) (hu : norm σ hσ u = 1) : u ≠ 0 := by
  intro h
  have he := congrArg Subtype.val hu
  simp [norm, h] at he

/-- Rotation of the norm plane, fixing both diagonal coordinates. -/
def normRotationLinear (u : E) (hu : norm σ hσ u = 1) :
    Space σ hσ ≃ₗ[fixedField σ] Space σ hσ where
  toFun X := (coordinates σ hσ).symm ((coordinates σ hσ X).1, u * (coordinates σ hσ X).2)
  invFun X := (coordinates σ hσ).symm ((coordinates σ hσ X).1, σ u * (coordinates σ hσ X).2)
  left_inv X := by
    have h : σ u * u = 1 := (mul_comm _ _).trans (congrArg Subtype.val hu)
    apply (coordinates σ hσ).injective
    simp [← mul_assoc, h]
  right_inv X := by
    have h : u * σ u = 1 := congrArg Subtype.val hu
    apply (coordinates σ hσ).injective
    simp [← mul_assoc, h]
  map_add' X Y := by
    apply (coordinates σ hσ).injective
    simp [mul_add]
  map_smul' c X := by
    apply (coordinates σ hσ).injective
    simp [Subfield.smul_def, mul_left_comm]

@[simp] theorem coordinates_normRotationLinear (u : E) (hu : norm σ hσ u = 1)
    (X : Space σ hσ) :
    coordinates σ hσ (normRotationLinear σ hσ u hu X) =
      ((coordinates σ hσ X).1, u * (coordinates σ hσ X).2) :=
  (coordinates σ hσ).apply_symm_apply _

/-- Norm-plane rotations as elements of the full orthogonal group. -/
def normRotation (u : E) (hu : norm σ hσ u = 1) :
    Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ) :=
  ⟨normRotationLinear σ hσ u hu,
    (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (by
      intro X
      apply neg_injective
      change -(-(form σ hσ _)) = -(-(form σ hσ _))
      rw [neg_neg, neg_neg, form_eq_coordinates, form_eq_coordinates,
        coordinates_normRotationLinear]
      congr 1
      apply Subtype.ext
      change (u * (coordinates σ hσ X).2) * σ (u * (coordinates σ hσ X).2) =
        (coordinates σ hσ X).2 * σ (coordinates σ hσ X).2
      rw [map_mul]
      have h : u * σ u = 1 := congrArg Subtype.val hu
      calc
        _ = (u * σ u) * ((coordinates σ hσ X).2 * σ (coordinates σ hσ X).2) := by ring
        _ = _ := by rw [h, one_mul])⟩

@[simp] theorem coordinates_normRotation (u : E) (hu : norm σ hσ u = 1)
    (X : Space σ hσ) :
    coordinates σ hσ ((normRotation σ hσ u hu).val X) =
      ((coordinates σ hσ X).1, u * (coordinates σ hσ X).2) :=
  coordinates_normRotationLinear σ hσ u hu X

@[simp] theorem coordinates_conjugation (X : Space σ hσ) :
    coordinates σ hσ ((conjugationOrthogonal σ hσ).val X) =
      ((coordinates σ hσ X).1, σ (coordinates σ hσ X).2) := by
  apply Prod.ext
  · rfl
  · exact (entry_conjugate σ hσ X 1 0).symm

theorem normRotation_commute (u v : E) (hu : norm σ hσ u = 1)
    (hv : norm σ hσ v = 1) :
    Commute (normRotation σ hσ u hu) (normRotation σ hσ v hv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply (coordinates σ hσ).injective
  change coordinates σ hσ ((normRotation σ hσ u hu).val ((normRotation σ hσ v hv).val X)) =
    coordinates σ hσ ((normRotation σ hσ v hv).val ((normRotation σ hσ u hu).val X))
  simp [mul_left_comm]

theorem conjugation_normRotation (u : E) (hu : norm σ hσ u = 1) :
    conjugationOrthogonal σ hσ * normRotation σ hσ u hu =
      (normRotation σ hσ u hu)⁻¹ * conjugationOrthogonal σ hσ := by
  apply (eq_inv_mul_iff_mul_eq).mpr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply (coordinates σ hσ).injective
  change coordinates σ hσ ((normRotation σ hσ u hu).val
    ((conjugationOrthogonal σ hσ).val ((normRotation σ hσ u hu).val X))) = _
  have h : u * σ u = 1 := congrArg Subtype.val hu
  simp [map_mul, ← mul_assoc, h]

/-- A determinant-one diagonal congruence acts by the square on the norm plane. -/
theorem coordinates_diagonal_action (u : E) (hu0 : u ≠ 0)
    (hu : norm σ hσ u = 1) (X : Space σ hσ) :
    coordinates σ hσ (action σ hσ (Matrix.SpecialLinearGroup.diag2 u hu0) X) =
      ((coordinates σ hσ X).1, u ^ 2 * (coordinates σ hσ X).2) := by
  have hc : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hu)
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
      field_simp
    · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
      field_simp
  · simp [coordinates, action_apply, Matrix.SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, adjoint, hc]
    ring

theorem normRotation_sq_mem_range (u : E) (hu : norm σ hσ u = 1) :
    normRotation σ hσ u hu * normRotation σ hσ u hu ∈ (orthogonalAction σ hσ).range := by
  refine ⟨Matrix.SpecialLinearGroup.diag2 u (norm_one_ne_zero σ hσ u hu), ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply (coordinates σ hσ).injective
  change coordinates σ hσ (action σ hσ _ X) =
    coordinates σ hσ ((normRotation σ hσ u hu).val ((normRotation σ hσ u hu).val X))
  rw [coordinates_diagonal_action σ hσ u _ hu, coordinates_normRotation, coordinates_normRotation]
  simp [pow_two, mul_assoc]


private def rotationMatrix (u : E) : Mat E := !![u, 0; 0, 1]

private lemma rotationMatrix_mul_adjoint (u : E) (hu : norm σ hσ u = 1) :
    rotationMatrix u * adjoint σ (rotationMatrix u) = 1 := by
  have h : u * σ u = 1 := congrArg Subtype.val hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, adjoint, Matrix.mul_apply, Fin.sum_univ_two, h]

private lemma adjoint_mul_rotationMatrix (u : E) (hu : norm σ hσ u = 1) :
    adjoint σ (rotationMatrix u) * rotationMatrix u = 1 := by
  have h : σ u * u = 1 := (mul_comm _ _).trans (congrArg Subtype.val hu)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, adjoint, Matrix.mul_apply, Fin.sum_univ_two, h]

private lemma normRotation_congruence (u : E) (hu : norm σ hσ u = 1)
    (X : Space σ hσ) :
    ((normRotation σ hσ u hu).val X).val =
      rotationMatrix u * X.val * adjoint σ (rotationMatrix u) := by
  have h : u * σ u = 1 := congrArg Subtype.val hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normRotation, normRotationLinear, coordinates, rotationMatrix,
      adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_mul,
      entry_conjugate σ hσ X 1 0]
  linear_combination -(X.val 0 0) * h
  exact mul_comm _ _

/-- Conjugation of SL₂ by the norm-one general linear diagonal matrix. -/
def rotationTwist (u : E) (hu : norm σ hσ u = 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) E) : Matrix.SpecialLinearGroup (Fin 2) E :=
  ⟨rotationMatrix u * A.val * adjoint σ (rotationMatrix u), by
    rw [Matrix.det_mul, Matrix.det_mul]
    have h := congrArg Matrix.det (rotationMatrix_mul_adjoint σ hσ u hu)
    rw [Matrix.det_mul, Matrix.det_one] at h
    rw [A.property, mul_one, h]⟩

/-- Norm-plane rotations normalize the literal SL₂ congruence image. -/
theorem normRotation_mul_action (u : E) (hu : norm σ hσ u = 1)
    (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    normRotation σ hσ u hu * orthogonalAction σ hσ A =
      orthogonalAction σ hσ (rotationTwist σ hσ u hu A) * normRotation σ hσ u hu := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change ((normRotation σ hσ u hu).val (action σ hσ A X)).val =
    (action σ hσ (rotationTwist σ hσ u hu A) ((normRotation σ hσ u hu).val X)).val
  rw [normRotation_congruence, action_apply, action_apply, normRotation_congruence]
  change _ = (rotationMatrix u * A.val * adjoint σ (rotationMatrix u)) *
    (rotationMatrix u * X.val * adjoint σ (rotationMatrix u)) *
      adjoint σ (rotationMatrix u * A.val * adjoint σ (rotationMatrix u))
  rw [adjoint_mul, adjoint_mul, adjoint_involutive σ hσ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adjoint σ (rotationMatrix u)) (rotationMatrix u),
    adjoint_mul_rotationMatrix σ hσ u hu, Matrix.one_mul]
  rw [← Matrix.mul_assoc (adjoint σ (rotationMatrix u)) (rotationMatrix u),
    adjoint_mul_rotationMatrix σ hσ u hu, Matrix.one_mul]

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
