module

public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.Frames
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.CommutatorImage.NormPlane
import Mathlib.Tactic.Group

/-!
# The Hermitian SL₂ image is the full orthogonal commutator

SL₂ congruences move any normalized singular pair to the two diagonal matrix
units. Their pointwise stabilizer consists of diagonal congruences, possibly
followed by field conjugation. Hence every determinant isometry has one of
these two forms. Conjugation normalizes the SL₂ image, so this image is normal
and its quotient has at most two elements. The full orthogonal commutator
therefore lies in the image. The reverse containment follows from the already
proved perfectness of SL₂ over GF(2^(2n)). Both arguments include n = 1.

This proves the actual image equality behind the identification
SL₂(q²) ≃ Omega₄⁻(q) in Aschbacher--Smith, I.1.6(3), printed p.408, used for
the minus orthogonal blocks of C.1.30 and F.1.12(I)(6), printed pp.135 and 263.
Omega here is literally the commutator of the full determinant-isometry group.
The comparison with the separately chosen minus quadratic form remains with
the parent assembly module.
-/

public noncomputable section

namespace Representation.OrthogonalFourMinus.HermitianEquiv
open FiniteModel
open ClassicalOrthogonal.Minus (Orthogonal)

-- Keep the quotient calculation abstract: unfolding the concrete matrix and
-- subgroup instances during the group algebra is unnecessarily expensive.
section TwoCosets
variable {S G : Type*} [Group S] [Group G]

private theorem normal_of_two_cosets (f : S →* G) (c : G) (σ : S → S)
    (hc : ∀ a, c * f a = f (σ a) * c)
    (hcover : ∀ g, ∃ a, g = f a ∨ g = f a * c) : f.range.Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    obtain ⟨b, rfl | rfl⟩ := hcover g
    · exact ⟨b * a * b⁻¹, by simp⟩
    · refine ⟨b * σ a * b⁻¹, ?_⟩
      have hca : c * f a * c⁻¹ = f (σ a) := by
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      simp only [map_mul, map_inv]
      rw [← hca]
      group

private theorem commutator_le_of_two_cosets (f : S →* G) (c : G) (σ : S → S)
    (hc : ∀ a, c * f a = f (σ a) * c)
    (hcover : ∀ g, ∃ a, g = f a ∨ g = f a * c) : commutator G ≤ f.range := by
  let : f.range.Normal := normal_of_two_cosets f c σ hc hcover
  let q := QuotientGroup.mk' f.range
  have hq (g : G) : q g = 1 ∨ q g = q c := by
    obtain ⟨a, rfl | rfl⟩ := hcover g
    · exact Or.inl ((QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩)
    · right
      rw [map_mul, show q (f a) = 1 from
        (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩, one_mul]
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective f.range x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective f.range y
  change q g * q h = q h * q g
  rcases hq g with hg | hg <;> rcases hq h with hh | hh <;> simp [hg, hh]

end TwoCosets

variable (n : ℕ) [NeZero n]

/-- Every Hermitian determinant isometry is an SL₂ congruence, possibly
followed by entrywise conjugation. -/
theorem orthogonal_normal_form
    (g : Orthogonal (fixedField n) (Space n) (form n)) :
    ∃ A, g = orthogonalAction n A ∨
      g = orthogonalAction n A * conjugationOrthogonal n := by
  obtain ⟨A, hA0, hA1⟩ := orthogonal_diagonal_pair_transitivity n g
  have h0 : ((orthogonalAction n A)⁻¹ * g).val (firstDiagonal n) = firstDiagonal n := by
    change (orthogonalAction n A).val.symm (g.val (firstDiagonal n)) = _
    rw [← hA0, LinearEquiv.symm_apply_apply]
  have h1 : ((orthogonalAction n A)⁻¹ * g).val (secondDiagonal n) = secondDiagonal n := by
    change (orthogonalAction n A).val.symm (g.val (secondDiagonal n)) = _
    rw [← hA1, LinearEquiv.symm_apply_apply]
  obtain ⟨B, hB | hB⟩ := diagonal_stabilizer_normal_form n ((orthogonalAction n A)⁻¹ * g) h0 h1
  · refine ⟨A * B, Or.inl ?_⟩
    exact (inv_mul_eq_iff_eq_mul.mp hB).trans (map_mul (orthogonalAction n) A B).symm
  · refine ⟨A * B, Or.inr ?_⟩
    exact (inv_mul_eq_iff_eq_mul.mp hB).trans
      ((mul_assoc _ _ _).symm.trans
        (congrArg (· * conjugationOrthogonal n) (map_mul (orthogonalAction n) A B).symm))


/-- The concrete Hermitian SL₂ image is normal in the full orthogonal group. -/
theorem range_orthogonalAction_normal : (orthogonalAction n).range.Normal :=
  normal_of_two_cosets (orthogonalAction n) (conjugationOrthogonal n)
    (Matrix.SpecialLinearGroup.map (conjugation n).toRingHom)
    (conjugationOrthogonal_mul_action n) (orthogonal_normal_form n)

/-- Every element of the full orthogonal commutator is an SL₂ congruence. -/
theorem commutator_le_range_orthogonalAction :
    commutator (Orthogonal (fixedField n) (Space n) (form n)) ≤
      (orthogonalAction n).range :=
  commutator_le_of_two_cosets (orthogonalAction n) (conjugationOrthogonal n)
    (Matrix.SpecialLinearGroup.map (conjugation n).toRingHom)
    (conjugationOrthogonal_mul_action n) (orthogonal_normal_form n)

/-- The action image is exactly Omega, defined as the full orthogonal commutator. -/
theorem range_orthogonalAction_eq_commutator :
    (orthogonalAction n).range =
      commutator (Orthogonal (fixedField n) (Space n) (form n)) :=
  le_antisymm (range_orthogonalAction_le_commutator n)
    (commutator_le_range_orthogonalAction n)

/-- The faithful action constructed in `OrthogonalAction` exhausts actual Omega. -/
theorem omegaAction_surjective : Function.Surjective (omegaAction n) := by
  intro g
  obtain ⟨A, hA⟩ := commutator_le_range_orthogonalAction n g.property
  exact ⟨A, Subtype.ext hA⟩

end Representation.OrthogonalFourMinus.HermitianEquiv
