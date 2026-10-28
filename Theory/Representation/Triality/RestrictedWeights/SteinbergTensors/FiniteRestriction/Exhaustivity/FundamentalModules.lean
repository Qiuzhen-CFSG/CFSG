module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.HighestWeightConstruction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OrientationObstruction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.LeftAssembly

/-!
# Assembling fundamental rational D4 modules

The central fundamental weight is numbered `1`; the three outer fundamental
weights are numbered `0`, `2`, and `3`. `LeftAssembly` uses the actual adjoint
root tangent for the central weight and regular functions for the outer
weights, with the source-correct left embedding. Highest-root centralization
and outer-function existence remain explicit geometric obligations.

The original raw-coordinate conditional assembly below is preserved.
`OrientationObstruction` proves that the source inverse-coroot rank-one
compatibility forces raw highest-weight coordinates to be nonpositive.
The separate left embedding resolves that convention mismatch; it does not
by itself prove existence of the four fundamental modules.
Sources: GLS3, Theorem 1.14.6(e), and Examples 1.14.9(c)--(f).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The central-node and outer-node regular functions together construct all
four fundamental rational factors. Their geometric existence is still required. -/
theorem fundamentalRationalExistence_of_regularFunctions (S : Geometry K)
    (hcentral : ∃ f : K.PolynomialFunction,
      IsHighestWeightRegularFunction S (Pi.single 1 1) f)
    (houter : ∀ i : Fin 4, i ≠ 1 → ∃ f : K.PolynomialFunction,
      IsHighestWeightRegularFunction S (Pi.single i 1) f) :
    FundamentalRationalExistence S := by
  intro i
  have h : ∃ f : K.PolynomialFunction,
      IsHighestWeightRegularFunction S (Pi.single i 1) f := by
    by_cases hi : i = 1
    · simpa only [hi] using hcentral
    · exact houter i hi
  obtain ⟨f, hf⟩ := h
  exact rationalFactor_exists_of_regularFunction S f hf

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
