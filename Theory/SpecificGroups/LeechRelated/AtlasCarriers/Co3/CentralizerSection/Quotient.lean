module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearGeneration

/-!
# The Co₃ involution-centralizer quotient onto PSp₆(2)

In the fixed degree-276 ATLAS carrier, `involution = b²` has order two and
`numerator = ⟨b,c,d⟩` centralizes it. Restriction to its 36 fixed points gives
the surjection `pointQuotient`. The faithful action on even quadratic refinements
and generation by the three exact matrices identify that image with the full
binary symplectic group. Composing with its central quotient gives `quotientMap`,
with no remaining action, generation, or model-comparison premise.

The first isomorphism theorem identifies the quotient by the kernel normal
inside the numerator. This is the section needed from the nonsplit `2Sp₆(2)`
centralizer in GLS3 Table 5.3j, used in Aschbacher--Smith A.2.19, pp.40--41.
Equality with the whole centralizer and identification of the kernel with its
central involution are unnecessary for that application.
-/

@[expose] public section
noncomputable section
namespace Sporadic.LeechRelated.Co3.CentralizerSection

/-- The faithful symplectic action has exactly the actual fixed-point image. -/
theorem linearAction_range_eq : linearAction.range = pointGroup :=
  linearAction_range_of_generation linear_generators_generate

/-- An actual isomorphism from the fixed-point image to the full matrix group. -/
def pointGroupSymplecticEquiv : pointGroup ≃* LinearData.Sp :=
  pointGroupEquivOfGeneration linear_generators_generate

/-- The required central quotient of a subgroup centralizing the actual involution. -/
def quotientMap : numerator →* SymplecticQuotient :=
  symplecticQuotientMapOfGeneration linear_generators_generate

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  symplecticQuotientMapOfGeneration_surjective linear_generators_generate

/-- Relative normality is in `numerator`, the domain of the constructed map. -/
def quotientKernelEquiv : numerator ⧸ quotientMap.ker ≃* SymplecticQuotient :=
  QuotientGroup.quotientKerEquivOfSurjective quotientMap quotientMap_surjective

end Sporadic.LeechRelated.Co3.CentralizerSection
