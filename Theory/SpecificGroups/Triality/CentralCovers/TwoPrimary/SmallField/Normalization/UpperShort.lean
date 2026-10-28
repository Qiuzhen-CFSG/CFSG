module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.LongPair
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort.Transport
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort.HighestTrace
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort.Comparison

/-!
# Upper short-root exchanges in the canonical smallest triality cover

Weyl transport gives the first upper short-pair exchange from the highest
short-pair trace formula. Equality of the long and short commutators at one
then gives the second exchange for the normalized highest section. Both
remaining calculations are explicit premises here; this module does not yet
assert their discharge from `CommutingPairs` alone.

The core imports only the earlier long-pair normalization, allowing the final
normalization module to consume it without a cycle. Source: GLS3 §2.4.5(b),
§6.1; Aschbacher–Smith I.1.3 (PDF p.418).
-/

public section
open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G
local notation "hf" => universalProjection_surjective G
local notation "hk" => universalProjection_ker_le_center G

/-- The exact two requested pair exchanges, conditional on the two remaining
calculations in the covering group. -/
theorem upperShort_relations_of_trace_and_comparison
    (hcomm : CommutingPairs universalRootSections)
    (htrace : UpperShort.HighestShortTrace π hf hk)
    (hcompare : longPairHighest universalRootSections = highestLift π hf hk) :
    PairExchange (longPairSections hk universalRootSections hcomm) 0 3 ∧
      PairExchange (longPairSections hk universalRootSections hcomm) 2 3 :=
  UpperShort.relations_of_trace_and_comparison π hf hk hcomm htrace hcompare

/-- The two upper short-pair trace relations in the canonical smallest cover.

The highest short-pair trace and the identification of the long-pair highest
commutator are proved in the cover itself, so the only remaining input is the
ten commuting-pair hypothesis on the original sections. -/
theorem upperShort_relations
    (hcomm : CommutingPairs universalRootSections) :
    PairExchange (longPairSections hk universalRootSections hcomm) 0 3 ∧
      PairExchange (longPairSections hk universalRootSections hcomm) 2 3 := by
  exact upperShort_relations_of_trace_and_comparison hcomm
    (UpperShort.universal_highestShortTrace hcomm)
    (UpperShort.universal_longPairHighest_eq_highestLift hcomm)

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
