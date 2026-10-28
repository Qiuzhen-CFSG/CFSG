module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.RootDensity

/-!
# The source-facing restricted D4 density contract

Specialize root-operator density on arbitrary carriers to the actual rational
factors in `LeftRestrictedRootDensity`. All sixteen binary left highest weights
are covered. This extension keeps the adapter's contract, which imports the
root-density module, outside that module's own import dependencies.

Source: the restricted infinitesimal-simplicity argument for Steinberg §13.1,
used in GLS3 Theorem 2.8.5 and Corollary 2.8.6(a).
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
public section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Restricted root density for every actual rational factor, with the
source-correct left highest-weight convention. -/
theorem leftRestrictedRootDensity (S : D4Geometry K) : LeftRestrictedRootDensity S := by
  intro A a hv
  exact rootOperatorAlgebra_eq_top_of_left_basic_highWeight S A.action A.irreducible a hv

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
