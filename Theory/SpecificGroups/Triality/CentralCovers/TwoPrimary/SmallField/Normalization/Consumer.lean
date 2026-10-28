module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField

/-!
# Applying root normalization to the canonical kernel

This applies the two-stage normalization to the existing small-field kernel
consumer. The completed application discharges all five interacting-pair
calculations and retains only the independent ten-pair commutation hypothesis.
The earlier conditional application is preserved. Keeping this module separate
allows the small-field umbrella to import the normalization without a cycle.
Source: Aschbacher–Smith I.1.3 (PDF p.418), GLS3 §6.1.
-/

public section
open Triality.Standard PerfectCentralCovering
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "π" => universalProjection G
local notation "hk" => universalProjection_ker_le_center G

/-- Actual application to the literal canonical kernel. Both remaining relation
families are explicit and must be discharged by the normalization assembly. -/
theorem universal_not_two_dvd_kernel_of_remaining_relations
    (hcomm : CommutingPairs universalRootSections)
    (h03 : PairExchange (longPairSections hk universalRootSections hcomm) 0 3)
    (h23 : PairExchange (longPairSections hk universalRootSections hcomm) 2 3)
    (hlower : ∀ L : RootSections 1 Nat.zero_lt_one π,
      CommutingPairs L → UpperRelations L →
      ∃ M : RootSections 1 Nat.zero_lt_one π,
        L.longRoot = M.longRoot ∧ LowerRelations M) :
    ¬ 2 ∣ Nat.card (universalProjection G).ker := by
  apply smallField_universal_not_two_dvd_kernel_of_pair_calculations hcomm
  intro hc
  exact exists_normalizingAdjustment_of_remaining_relations hc h03 h23 hlower

/-- Normalization discharges the interacting-pair input of the canonical-kernel
consumer. The ten commuting pairs remain the independent source calculation. -/
theorem universal_not_two_dvd_kernel_of_commutingPairs
    (hcomm : CommutingPairs universalRootSections) :
    ¬ 2 ∣ Nat.card (universalProjection G).ker :=
  smallField_universal_not_two_dvd_kernel_of_pair_calculations hcomm
    exists_normalizingAdjustment

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
