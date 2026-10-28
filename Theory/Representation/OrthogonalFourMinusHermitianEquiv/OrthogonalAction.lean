module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.ProjectiveOmega
import Mathlib.Algebra.CharP.Two

/-!
# The Hermitian action inside the orthogonal commutator subgroup

The determinant-preserving SL₂ action takes values in the full quadratic
isometry group. SL₂ over GF(2^(2n)) is perfect, including n = 1: a nonfixed
field element supplies a diagonal element whose square is not one, and the
standard transvection commutator formula proves perfectness. Consequently
the Hermitian action factors faithfully through the orthogonal commutator.

This establishes one containment needed for the exceptional identification
SL₂(q²) ≃ Ω₄⁻(q). Surjectivity and comparison with the chosen minus form are
separate obligations. Source: Aschbacher--Smith, C.1.30 and F.1.12(I)(6),
combined manuscript of 1 March 2004, printed pp.135 and 263.
-/

@[expose] public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
open ClassicalOrthogonal.Minus (Orthogonal Omega)

variable (n : ℕ) [NeZero n]

/-- The Hermitian congruence action as an actual quadratic isometry. -/
def orthogonalAction : Matrix.SpecialLinearGroup (Fin 2) (Field n) →*
    Orthogonal (fixedField n) (Space n) (form n) where
  toFun A := ⟨linearActionHom n A,
    (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (form_preserved n A)⟩
  map_one' := Subtype.ext (map_one (linearActionHom n))
  map_mul' A B := Subtype.ext (map_mul (linearActionHom n) A B)

@[simp] theorem orthogonalAction_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    (orthogonalAction n A).val X = action n A X := rfl

theorem orthogonalAction_injective : Function.Injective (orthogonalAction n) := by
  intro A B h
  exact linearActionHom_injective n (congrArg Subtype.val h)

/-- Perfectness holds even at q = 2, since the matrix field has order q². -/
theorem sl2_commutator_eq_top :
    commutator (Matrix.SpecialLinearGroup (Fin 2) (Field n)) = ⊤ := by
  obtain ⟨t, ht⟩ := exists_conjugation_ne n
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (map_zero _)
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    have ht1 : t = 1 := CharTwo.sq_injective (by simpa using h)
    exact ht (by rw [ht1, map_one])
  exact Matrix.SL2.commutator_eq_top ht0 ht2

/-- Every element of the Hermitian action image belongs to Omega. -/
theorem range_orthogonalAction_le_commutator :
    (orthogonalAction n).range ≤
      commutator (Orthogonal (fixedField n) (Space n) (form n)) := by
  have h := map_commutator_eq _ (orthogonalAction n)
  rw [sl2_commutator_eq_top, ← MonoidHom.range_eq_map] at h
  rw [h, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

/-- The resulting faithful homomorphism into the actual commutator subgroup. -/
def omegaAction : Matrix.SpecialLinearGroup (Fin 2) (Field n) →*
    Omega (fixedField n) (Space n) (form n) where
  toFun A := ⟨orthogonalAction n A,
    range_orthogonalAction_le_commutator n ⟨A, rfl⟩⟩
  map_one' := Subtype.ext (map_one (orthogonalAction n))
  map_mul' A B := Subtype.ext (map_mul (orthogonalAction n) A B)

@[simp] theorem omegaAction_apply
    (A : Matrix.SpecialLinearGroup (Fin 2) (Field n)) (X : Space n) :
    (omegaAction n A).val.val X = action n A X := rfl

theorem omegaAction_injective : Function.Injective (omegaAction n) := by
  intro A B h
  exact orthogonalAction_injective n (congrArg Subtype.val h)

end Representation.OrthogonalFourMinus.HermitianEquiv
