module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.RegularFunctions

/-!
# Left highest weights from normalized regular functions

The same right translation orbit realizes the inverted character. Normalization,
positive-root invariance, and all actual torus equations are retained.
Source: GLS3 1.14.6(d)--(e), with Steinberg's direct convention (6.1).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
/-- A normalized regular function with the actual right highest-weight laws.
These are equations of regular functions on the given group, not assumptions
about existence or irreducibility of a representation. -/
structure IsLeftHighestWeightRegularFunction (S : Geometry K) (a : Weight)
    (f : K.PolynomialFunction) : Prop where
  at_one : f 1 = 1
  torus : ∀ (t : Variety.Point S.torus.carrierVariety) (x : Variety.Point K),
    f (x * S.torus.includePoint t) = (S.leftWeightEmbedding a).pointCharacter t * f x
  positive_root : ∀ r ∈ S.roots.positive,
    ∀ (v : Variety.Point (S.roots.rootSubgroup r).carrierVariety) (x : Variety.Point K),
      f (x * (S.roots.rootSubgroup r).includePoint v) = f x


omit [IsAlgClosed k] in
theorem isLeftHighestWeightRegularFunction_iff (S : Geometry K) (a : Weight)
    (f : K.PolynomialFunction) :
    IsLeftHighestWeightRegularFunction S a f ↔ IsHighestWeightRegularFunction S (-a) f :=
  ⟨fun h => ⟨h.at_one, h.torus, h.positive_root⟩,
    fun h => ⟨h.at_one, h.torus, h.positive_root⟩⟩

theorem leftRationalFactor_exists_of_regularFunction (S : Geometry K) {a : Weight}
    (f : K.PolynomialFunction) (hf : IsLeftHighestWeightRegularFunction S a f) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A a :=
  rationalFactor_exists_of_regularFunction S f ((isLeftHighestWeightRegularFunction_iff S a f).mp hf)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
