module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Orbit.Transport
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.SectionOfLifts
/-!
# A literal Fi22 quotient in an involution centralizer of Fi24′

The original first ATLAS generator is an involution. Two certified Bray
words centralize it and preserve an injectively labeled set of 3510 letters;
the lifting words act there as the original Fi22 generators. Their generated
subgroup consequently maps onto the actual Fi22 permutation carrier.

This is the source datum required in Aschbacher--Smith A.2.19 and GLS3
Table 5.3u. No order, simplicity or whole-centralizer identification is used.
-/
public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection
open Subgroup

theorem exists_source_section :
    ∃ (t : Carrier) (L : Subgroup Carrier) (f : L →* Fi22.Carrier),
      orderOf t = 2 ∧ L ≤ centralizer ({t} : Set Carrier) ∧
      Function.Surjective f :=
  exists_source_section_of_lifts a liftA liftB a_order
    (liftA_centralizes Bray.h0_centralizes Bray.h1_centralizes)
    (liftB_centralizes Bray.h0_centralizes Bray.h1_centralizes)
    Orbit.point Orbit.point_injective Orbit.liftA_action Orbit.liftB_action
end Sporadic.Fischer.Fi24Prime.CentralizerSection
