module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.HighestLift
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Pairs

/-!
# From the small-field pair calculations to the canonical kernel

A central adjustment preserves additivity and the six prescribed root
projections. Its exact higher-root relations give a section of the literal
positive subgroup, whose odd index permits central transfer. These conditional
reductions are shared by the pair calculations and their unconditional assembly
in `SmallField`, avoiding an import cycle while retaining their public names.

Sources: Aschbacher–Smith A.2.4 and I.1.3 (PDF pp.44 and 418), GLS3 §2.4
and §6.1, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open PerfectCentralCovering

local notation "G" => BinaryCarrier 1 Nat.zero_lt_one

/-- A central normalization of the constructed lifts supplies the exact witness. -/
theorem smallField_higherCommutators_of_adjustment
    (h : ∃ A : SmallField.CentralAdjustment (universalProjection G),
      (A.adjusted (universalProjection_ker_le_center G)
        SmallField.universalRootSections).HigherCommutators) :
    ∃ L : RootSections 1 (by decide)
      (universalProjection (BinaryCarrier 1 (by decide))), L.HigherCommutators := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.adjusted (universalProjection_ker_le_center G)
    SmallField.universalRootSections, hA⟩

/-- The two remaining pair calculations imply exclusion on the literal kernel. -/
theorem smallField_universal_not_two_dvd_kernel_of_pair_calculations
    (hcomm : SmallField.CommutingPairs SmallField.universalRootSections)
    (hnormalize : SmallField.CommutingPairs SmallField.universalRootSections →
      ∃ A : SmallField.CentralAdjustment (universalProjection G),
        (A.adjusted (universalProjection_ker_le_center G)
          SmallField.universalRootSections).HigherCommutators) :
    ¬ 2 ∣ Nat.card (universalProjection (BinaryCarrier 1 (by decide))).ker := by
  obtain ⟨L, hL⟩ := smallField_higherCommutators_of_adjustment (hnormalize hcomm)
  exact universal_not_two_dvd_kernel_of_higherCommutators 1 (by decide) L hL

end Triality.Standard.CentralCovers.TwoPrimary
