module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# The HS outer restriction

Every automorphism of the fixed degree-100 ATLAS carrier preserves its
point-stabilizer family and is therefore induced by a normalizing permutation.
The carrier has index dividing two in its permutation normalizer, so its
actual outer automorphism group is a two-group. Transport through the supplied
group isomorphism gives the cyclic-normal odd-quotient condition used in
Proposition 1.3.4.

The conditional reduction is retained, and the final theorem discharges both
model premises using the checked point-stabilizer and normalizer calculations.
Sources: Aschbacher–Smith, combined 1 March 2004
manuscript, printed pp.33 and 510; GLS3, Table 5.3m, printed p.274.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory Sporadic.LeechRelated

/-- The permutation-model route, transported to the actual group in the consumer. -/
theorem higmanSims_outer_cyclicNormalOddQuotient_of_pointStabilizers
    {S : Type*} [Group S] (e : S ≃* HS.Carrier)
    (h : ∀ α : MulAut HS.Carrier, ∃ y : Fin 100,
      HS.pointStabilizer.map α.toMonoidHom = MulAction.stabilizer HS.Carrier y)
    (hi : ∃ n : ℕ,
      HS.generated.relIndex (normalizer (HS.generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 ^ n) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  (hasCyclicNormalOddQuotient_of_isPGroup_two
    (HS.outer_isPGroup_two_of_pointStabilizer_map h hi)).of_injective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The fixed HS carrier satisfies the outer restriction, transported through
the actual model isomorphism. No additional model premises are required. -/
theorem higmanSims_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* HS.Carrier) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  higmanSims_outer_cyclicNormalOddQuotient_of_pointStabilizers e
    HS.pointStabilizer_map HS.normalizer_relIndex_dvd_two_pow

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
