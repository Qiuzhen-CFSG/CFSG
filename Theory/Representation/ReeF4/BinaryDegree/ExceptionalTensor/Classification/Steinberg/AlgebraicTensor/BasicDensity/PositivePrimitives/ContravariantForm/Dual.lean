module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.AlgebraicFactors

/-!
# The rational dual of an actual F₄ factor

The contragredient action on the linear dual is rational and irreducible, so it
is again an `AlgebraicFactor`. Its defining equation evaluates a covector on the
inverse action on the original space. The space is literally the linear dual;
no self-duality or highest-weight identification is asserted here.

This is the rational-duality input to the contravariant-form construction for
the primitive-vector argument in Steinberg, *Representations of Algebraic
Groups*, Nagoya Math. J. 22 (1963), §§2, 4, and 11.1,
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.ContravariantForm
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- The actual rational contragredient factor, on the linear dual space. -/
@[expose] def dualFactor (B : AlgebraicFactor F) : AlgebraicFactor F where
  Space := Module.Dual F B.Space
  action := (rationalRepresentation_dual_exists B.action B.irreducible.1).choose
  irreducible := dualRepresentation_isIrreducible B.action _
    (rationalRepresentation_dual_exists B.action B.irreducible.1).choose_spec.1
    B.irreducible
    (rationalRepresentation_dual_exists B.action B.irreducible.1).choose_spec.2

/-- Evaluation of the dual action uses precisely the inverse original action. -/
theorem dualFactor_spec (B : AlgebraicFactor F) :
    IsDualRepresentation B.action (dualFactor B).action :=
  (rationalRepresentation_dual_exists B.action B.irreducible.1).choose_spec.1

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.ContravariantForm
