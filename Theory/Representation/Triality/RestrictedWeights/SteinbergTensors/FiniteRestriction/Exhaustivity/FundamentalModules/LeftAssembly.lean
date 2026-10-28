module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.CentralRoot
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.RegularFunctions

/-!
# Assembling the four positive left fundamental weights

The central factor is constructed from the actual highest-root tangent.
The three outer factors are constructed from normalized regular functions
using their finite rational translation orbits. This separates two independent
geometric obligations: centralization of the highest-root subgroup and
existence of the three outer functions. Both premises must be discharged
before asserting fundamental existence from `Geometry` alone.

All characters use the corrected left embedding and the original Borel.
Sources: GLS3, Theorem 1.14.6(d)--(e), Examples 1.14.9(c),(d),(f), and
Steinberg (6.1), §13.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The two geometric constructions supply actual rational irreducibles at
each of the four positive fundamental left weights. -/
theorem leftFundamentalRationalExistence_of_centralizes_of_outerRegularFunctions
    (S : Geometry K) (hc : FundamentalModules.PositiveCentralizesHighestRoot S)
    (ho : ∀ i : Fin 4, i ≠ 1 → ∃ f : K.PolynomialFunction,
      IsLeftHighestWeightRegularFunction S (Pi.single i 1) f) :
    LeftFundamentalRationalExistence S := by
  intro i
  by_cases hi : i = 1
  · subst i
    exact FundamentalModules.centralLeftRationalFactor_exists_of_centralizes S hc
  · obtain ⟨f, hf⟩ := ho i hi
    exact leftRationalFactor_exists_of_regularFunction S f hf

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
