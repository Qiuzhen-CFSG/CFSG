module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalInput
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.Diagram

/-!
# Outer fundamental regular functions from the natural D4 action

A normalized matrix coefficient of the natural highest vector has left weight
`Pi.single 0 1`. Pulling back along the actual regular diagram automorphism
once and twice gives weights `Pi.single 3 1` and `Pi.single 2 1`, with the
same positive root groups and Borel. The torus and character compatibilities
are proved in `Diagram` from the supplied geometry.

Construction of `NaturalModule S` for arbitrary `S` remains required before
asserting unconditional `leftOuterRegularFunction_exists`. The theorem here
records the complete assembly from that explicit geometric input.

Sources: GLS3, Theorem 1.14.6(e), Examples 1.14.9(d),(f);
Steinberg, (6.1) and §13, `refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual natural action and actual graph pullback supply all three arms.
This is conditional on construction of the natural action on the given group. -/
theorem leftOuterRegularFunction_exists_of_naturalModule (S : Geometry K)
    (N : OuterFunctions.NaturalModule S) (i : Fin 4) (hi : i ≠ 1) :
    ∃ f : K.PolynomialFunction,
      IsLeftHighestWeightRegularFunction S (Pi.single i 1) f := by
  obtain ⟨f, hf⟩ := N.regularFunction_exists
  exact OuterFunctions.outerRegularFunction_exists_of_zero S f hf i hi

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
