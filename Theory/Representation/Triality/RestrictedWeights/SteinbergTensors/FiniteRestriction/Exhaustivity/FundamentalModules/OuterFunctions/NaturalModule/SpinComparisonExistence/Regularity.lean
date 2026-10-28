module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.LocalMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Regularity.ProductLift
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.Regularity.PrincipalOpen

/-!
# Global regularity reduced to an actual root-product chart

The regular Spin-valued product agrees with the supplied point homomorphism
on every torus/root product. A regular section of the source product map on
one nonempty principal open therefore gives local regularity of that
homomorphism. Translation and polynomial denominator descent then produce
its global algebraic-group morphism.

The source chart is an explicit geometric premise here. It is not supplied
by density or pointwise coordinate uniqueness, and existence of that chart
must be established before asserting `RootwiseSpinHom.exists_morphism`.

Source: Steinberg (6.1)--(6.2), `refs/KGroup/GLS3/Chapter2St2.tex`; GLS3
Theorem 1.10.7(d) and Example 1.14.9(d), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Triality.SimplyConnected
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
namespace SpinComparisonExistence

/-- A regular section of an actual root product on a nonempty principal open
suffices to globalize the supplied marked homomorphism. The chart-existence
obligation remains explicit. -/
theorem RootwiseSpinHom.exists_morphism_of_rootProduct_section
    {S : Geometry K} (C : RootwiseSpinHom k S)
    (positive negative : List S.roots.Root)
    (p : MvPolynomial K.Coordinates k)
    (hp : ∃ z : Variety.Point K, evalPolynomial z.val p ≠ 0)
    (s : Variety.Morphism (K.principalOpenChart p) S.rootProductParameterSpace)
    (hs : ∀ x, (S.rootProductMorphism positive negative).toFun (s.toFun x) =
      (K.principalOpenChartInclusion p).toFun x) :
    ∃ f : Morphism K (groupVariety k), f.onPoints = C.pointHom := by
  apply Morphism.exists_of_nonempty_principalOpen C.pointHom p hp
    ((C.parameterMorphism positive negative).comp s)
  intro x
  change (C.parameterMorphism positive negative).toFun (s.toFun x) = _
  rw [C.parameterMorphism_apply, hs]

end SpinComparisonExistence
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
