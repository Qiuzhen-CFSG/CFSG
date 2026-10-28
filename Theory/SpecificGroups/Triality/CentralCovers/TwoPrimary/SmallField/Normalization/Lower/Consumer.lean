module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Consumer

/-!
# Applying lower normalization to the smallest triality kernel

The arms-torus construction and the two lower polynomial calculations now
discharge lower normalization. Only the two upper short-pair premises remain
explicit in the final applications below. The upper premises are owned by
`qt-i01-triality-small-upper-short-relations`; final normalization assembly
retains their discharge. Source: Aschbacher–Smith I.1.3 (PDF p.418), GLS3 §6.1.
-/

public section
open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
open LowerNormalization
noncomputable section
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G
local notation "hk" => universalProjection_ker_le_center G

/-- The literal central-adjustment consumer, with the remaining calculations explicit. -/
theorem exists_normalizingAdjustment_of_torus_calculations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3)
    (hshort : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M → ShortPairRelation M)
    (hmixed : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M →
        ShortPairRelation M → MixedPairRelation M) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators :=
  exists_normalizingAdjustment_of_remaining_relations hcomm h03 h23
    (exists_lowerNormalized_of_torus_calculations hshort hmixed)

/-- Application to the actual canonical kernel, without assuming a multiplier table. -/
theorem universal_not_two_dvd_kernel_of_torus_calculations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3)
    (hshort : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M → ShortPairRelation M)
    (hmixed : ∀ M : RootSections 1 Nat.zero_lt_one π,
      ArmsTorusNormalized M → CommutingPairs M → UpperRelations M →
        ShortPairRelation M → MixedPairRelation M) :
    ¬ 2 ∣ Nat.card (universalProjection G).ker :=
  universal_not_two_dvd_kernel_of_remaining_relations hcomm h03 h23
    (exists_lowerNormalized_of_torus_calculations hshort hmixed)

/-- Lower normalization supplies the literal central-adjustment consumer;
the two upper short-pair relations remain explicit for final assembly. -/
theorem exists_normalizingAdjustment_of_upper_relations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3) :
    ∃ A : CentralAdjustment π,
      (A.adjusted hk universalRootSections).HigherCommutators :=
  exists_normalizingAdjustment_of_remaining_relations hcomm h03 h23 exists_lowerNormalized

/-- The canonical two-primary kernel application, with only the upper
short-pair calculations left to the normalization assembly. -/
theorem universal_not_two_dvd_kernel_of_upper_relations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3) :
    ¬ 2 ∣ Nat.card (universalProjection G).ker :=
  universal_not_two_dvd_kernel_of_remaining_relations hcomm h03 h23 exists_lowerNormalized

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
