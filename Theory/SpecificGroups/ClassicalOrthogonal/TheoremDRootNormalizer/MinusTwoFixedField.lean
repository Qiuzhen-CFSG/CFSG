module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness

/-!
# The projective minus-four comparison over the actual Frobenius fixed field

The determinant action on Hermitian two-by-two matrices already identifies
SL₂(2^(2n)) with the full commutator subgroup of the chosen minus-four form
over the Frobenius fixed field of order 2^n. Both scalar kernels are trivial
in characteristic two, giving the actual projective group equivalence.

This is the canonical-field case of the rank-one minus alias needed in
Theorem D. Transport from an arbitrary field of order 2^n is a separate
obligation; equality of field orders is not used as equality of carriers.
Sources: GLS3 §2.7; Aschbacher–Smith I.1.6(3), printed p.408.
-/

@[expose] public noncomputable section

namespace ClassicalOrthogonal.TheoremDRootNormalizer
open Representation.OrthogonalFourMinus

/-- An equivalence of the literal scalar quotients, including exponent one. -/
def minusTwoFixedFieldEquivPSL (n : ℕ) [NeZero n] :
    ClassicalGroup.POmegaMinus 2 (FiniteModel.fixedField n) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (FiniteModel.Field n) :=
  (minusOmegaEquivProjective 2).symm.trans
    ((HermitianEquiv.sl2EquivMinusOmega n).symm.trans (FiniteModel.sl2EquivPSL2 n))

/-- The comparison retains the actual SL₂ action and both projective maps. -/
@[simp] theorem minusTwoFixedFieldEquivPSL_apply (n : ℕ) [NeZero n]
    (g : Matrix.SpecialLinearGroup (Fin 2) (FiniteModel.Field n)) :
    minusTwoFixedFieldEquivPSL n
      (minusOmegaEquivProjective 2 (HermitianEquiv.sl2EquivMinusOmega n g)) =
      QuotientGroup.mk g := by
  simp only [minusTwoFixedFieldEquivPSL, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, FiniteModel.sl2EquivPSL2_apply]

end ClassicalOrthogonal.TheoremDRootNormalizer
