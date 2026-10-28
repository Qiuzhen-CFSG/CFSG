module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2

/-!
# The compatible Hall--Janko output of the sporadic sieve

The local inspection in 15.3.42 must identify the actual component quotient
with the full automorphism group of the fixed ATLAS J₂ carrier. Its restriction
to the simple component must agree with inner automorphisms under the same
component identification. This output interface retains both maps and their
compatibility, so the subsequent action calculation can be developed with
this witness as an explicit input.

No existence, order, simplicity or local subgroup theorem is asserted here.
Source: Aschbacher--Smith, combined manuscript, 15.3.42, printed p.1138.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo

variable {G : Type*} [Group G]

/-- The two actual model isomorphisms, with the component's inner action.
Construction belongs to the local sporadic sieve, not to this record. -/
structure JankoTwoIdentification (I L : Subgroup G) [(L.subgroupOf I).Normal] where
  equivalence : ComponentQuotient I L ≃* MulAut Sporadic.LeechRelated.J2.Carrier
  component : componentImage I L L ≃* Sporadic.LeechRelated.J2.Carrier
  inner_compatible : ∀ x : componentImage I L L,
    equivalence (x : ComponentQuotient I L) = MulAut.conj (component x)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo
