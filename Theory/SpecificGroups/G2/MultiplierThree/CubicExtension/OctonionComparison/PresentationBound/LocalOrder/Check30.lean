module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_30720 : checkChunk context facts instructions 30720 128 = true := by decide +kernel

theorem checked_30848 : checkChunk context facts instructions 30848 128 = true := by decide +kernel

theorem checked_30976 : checkChunk context facts instructions 30976 128 = true := by decide +kernel

theorem checked_31104 : checkChunk context facts instructions 31104 128 = true := by decide +kernel

theorem checked_31232 : checkChunk context facts instructions 31232 128 = true := by decide +kernel

theorem checked_31360 : checkChunk context facts instructions 31360 128 = true := by decide +kernel

theorem checked_31488 : checkChunk context facts instructions 31488 128 = true := by decide +kernel

theorem checked_31616 : checkChunk context facts instructions 31616 128 = true := by decide +kernel

theorem holds_block_30720 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 30720 → Holds H g ρ (facts n)) :
    ∀ n, n < 31744 → Holds H g ρ (facts n) := by
  have hall_30720 := checkChunk_sound valid facts instructions 30720 128 prior checked_30720
  have hall_30848 := checkChunk_sound valid facts instructions 30848 128 hall_30720 checked_30848
  have hall_30976 := checkChunk_sound valid facts instructions 30976 128 hall_30848 checked_30976
  have hall_31104 := checkChunk_sound valid facts instructions 31104 128 hall_30976 checked_31104
  have hall_31232 := checkChunk_sound valid facts instructions 31232 128 hall_31104 checked_31232
  have hall_31360 := checkChunk_sound valid facts instructions 31360 128 hall_31232 checked_31360
  have hall_31488 := checkChunk_sound valid facts instructions 31488 128 hall_31360 checked_31488
  have hall_31616 := checkChunk_sound valid facts instructions 31616 128 hall_31488 checked_31616
  exact hall_31616

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
