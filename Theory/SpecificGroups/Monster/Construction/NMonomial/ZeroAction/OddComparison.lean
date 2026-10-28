module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.Descent
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.Stability
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.GeneratorFormulas

/-!
# The marked odd-family comparison and its actual local restriction

Signed coordinate descent constructs oddComparison on the literal odd short
span, with its exact generator equation and form identity. The genuine local
C-action preserves this span. Its tensor transport therefore has the literal
quotient conjugation action on marked vectors, and agrees with a separately
constructed model whenever both satisfy the independently specified signed
generator formulas. The comparison also discharges the odd-isometry premise
of the parent's zeroToModel map.

The group identities of 29.6 remain a separate input to the generator formulas.
In particular, the conditional intertwining theorem here is not an assertion
of full 29.8 equivariance before those identities have been proved.

Source: Aschbacher, Sporadic Groups, 29.6--29.8, printed pp.156--157 (PDF
page 84), with the first-standard-generator convention explained in
GeneratorFormulas and the literal short lifts from Section 27.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction LocalC ShortFamilies TrialitySpin
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

attribute [local irreducible] oddRepresentation

/-- The actual restricted action expressed in the constructed tensor coordinates. -/
def oddTensorRepresentation : Representation ℝ N1 TensorTwo :=
  oddComparison.conjRingEquiv.toMonoidHom.comp oddRepresentation

theorem oddTensorRepresentation_apply (g : N1) (v : TensorTwo) :
    oddTensorRepresentation g v = oddComparison (oddRepresentation g (oddComparison.symm v)) := rfl

theorem oddTensorRepresentation_vector_of_conjugation
    (g : N1) (x y : Omega) (b c : ParkerLoop)
    (h : q1ImageConjugation g (rOddElement x b) = rOddElement y c) :
    oddTensorRepresentation g (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector y ⊗ₜ[ℝ] delta2 c := by
  rw [oddTensorRepresentation_apply, ← oddComparison_vector, LinearEquiv.symm_apply_apply,
    oddRepresentation_vector_of_conjugation g x y b c h, oddComparison_vector]

/-- A model with the independently specified generator formulas is equivariant
once the actual conjugation calculation supplies those formulas for the source. -/
theorem oddComparison_intertwines_of_formulas (ρ : Representation ℝ N1 TensorTwo)
    (hs : OddGeneratorFormulas oddTensorRepresentation) (hρ : OddGeneratorFormulas ρ)
    (g : N1) (v : oddSpace) :
    oddComparison (oddRepresentation g v) = ρ g (oddComparison v) := by
  have he := representation_eq_of_oddGeneratorFormulas oddTensorRepresentation ρ hs hρ
  rw [← he, oddTensorRepresentation_apply, LinearEquiv.symm_apply_apply]

/-- Instantiation of the parent's marked first-slot map with the constructed comparison. -/
theorem zeroToModel_oddComparison (x : Omega) (b : ParkerLoop) :
    zeroToModel oddComparison (zeroOdd x b) = modelOdd x b :=
  zeroToModel_odd oddComparison oddComparison_vector x b

theorem zeroToModel_oddComparison_isometry (v w : ZeroSpace) :
    modelGamma (zeroToModel oddComparison v) (zeroToModel oddComparison w) = zeroGamma v w :=
  zeroToModel_isometry oddComparison oddComparison_isometry v w

end Sporadic.Monster.Construction.NMonomial.ZeroAction
