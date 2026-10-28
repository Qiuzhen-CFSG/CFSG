module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Independence
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Parameters

/-!
# Independent tangent directions for the actual D4 geometry

The given maximal torus and the 24 realized root subgroups supply independent
tangent directions. Root characters are nontrivial even in characteristic two:
their integral pairing with their own cocharacter is two. Distinct characters
separate the root tangent lines, and the torus tangent has trivial character.

Consequently a geometric upper bound on the ambient tangent dimension proves
that these embedded subgroup tangents span. The upper bound remains explicit
here. The pointwise density in `Geometry.bigCell` has not been promoted to a
separability assertion. The missing upper bound can instead be obtained from
a dense morphism from `Geometry.rootProductParameterSpace` and smoothness of
algebraic groups; that route requires proving the root-product geometry.

Source: Steinberg 6.2(b--c), `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual torus and 24 distinct root tangent lines give the expected
lower bound, with no geometric spanning assumption. -/
public theorem Geometry.torus_root_tangent_finrank_lower_bound (S : Geometry K) :
    Module.finrank k (Bor1.IdentityPointDerivation S.torus.carrierVariety) + 24 ≤
      Module.finrank k (Bor1.IdentityPointDerivation K) := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  simpa only [S.root_card] using
    realized_torus_root_tangent_finrank_lower_bound S.roots S.realized
      S.maximalTorus.1 S.rootParameter

/-- The remaining geometric upper bound suffices for spanning by the actual
embedded torus and root-subgroup tangents. This is a conditional reduction,
not the unconditional tangent consequence of Steinberg 6.2. -/
public theorem Geometry.torus_root_tangent_span_of_finrank_le (S : Geometry K)
    (hdim : Module.finrank k (Bor1.IdentityPointDerivation K) ≤
      Module.finrank k (Bor1.IdentityPointDerivation S.torus.carrierVariety) + 24) :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap S.torus.inclusion) ⊔
      (⨆ a : S.roots.Root, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (S.roots.rootSubgroup a).inclusion)) = ⊤ := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  apply realized_torus_root_tangent_span_of_finrank_le S.roots S.realized
    S.maximalTorus.1 S.rootParameter
  simpa only [S.root_card] using hdim

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
