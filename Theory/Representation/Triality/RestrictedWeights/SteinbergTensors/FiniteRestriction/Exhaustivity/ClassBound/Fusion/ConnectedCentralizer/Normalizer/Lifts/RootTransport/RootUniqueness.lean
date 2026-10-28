module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.RootUniqueness.TangentLines

/-!
# Actual D4 root-subgroup uniqueness from tangent spanning

The integral character comparison and the actual root tangent lines establish
both multiplicity one and absence of higher inverse-root weights. Tangent
rigidity then identifies root parametrizations up to a nonzero scalar, hence
identifies their closed subgroups.

The remaining premise is precisely the independent geometric theorem that the
actual torus and root-subgroup tangents span. It is not part of `IsRealization`
and is not inferred here from pointwise big-cell density. The unconditional
`rootSubgroupUniqueness` assembly awaits that theorem from
`ConnectedLang.FrobeniusDifferential.TangentSpan`.

Source: GLS3, Definitions 1.9.1--1.9.3 and Theorem 1.9.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer.Normalizer

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual tangent spanning statement suffices for uniqueness of every
realized root subgroup. The geometric spanning premise remains explicit. -/
theorem rootSubgroupUniqueness_of_tangent_span (S : Geometry K)
    (hspan : LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) = ⊤) :
    RootSubgroupUniqueness S := by
  intro a X hX hweight
  exact RootWeightSpaceMultiplicityOne.rootSubgroup_eq
    (RootUniqueness.root_multiplicityOne_of_tangent_span S hspan a)
    hX hweight (S.realized.2.2.1 a).1 (S.realized.2.2.1 a).2

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
