module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_78848 : checkChunk context facts instructions 78848 128 = true := by decide +kernel

theorem checked_78976 : checkChunk context facts instructions 78976 128 = true := by decide +kernel

theorem checked_79104 : checkChunk context facts instructions 79104 128 = true := by decide +kernel

theorem checked_79232 : checkChunk context facts instructions 79232 128 = true := by decide +kernel

theorem checked_79360 : checkChunk context facts instructions 79360 128 = true := by decide +kernel

theorem checked_79488 : checkChunk context facts instructions 79488 128 = true := by decide +kernel

theorem checked_79616 : checkChunk context facts instructions 79616 128 = true := by decide +kernel

theorem checked_79744 : checkChunk context facts instructions 79744 128 = true := by decide +kernel

theorem holds_block_78848 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 78848 → Holds H g ρ (facts n)) :
    ∀ n, n < 79872 → Holds H g ρ (facts n) := by
  have hall_78848 := checkChunk_sound valid facts instructions 78848 128 prior checked_78848
  have hall_78976 := checkChunk_sound valid facts instructions 78976 128 hall_78848 checked_78976
  have hall_79104 := checkChunk_sound valid facts instructions 79104 128 hall_78976 checked_79104
  have hall_79232 := checkChunk_sound valid facts instructions 79232 128 hall_79104 checked_79232
  have hall_79360 := checkChunk_sound valid facts instructions 79360 128 hall_79232 checked_79360
  have hall_79488 := checkChunk_sound valid facts instructions 79488 128 hall_79360 checked_79488
  have hall_79616 := checkChunk_sound valid facts instructions 79616 128 hall_79488 checked_79616
  have hall_79744 := checkChunk_sound valid facts instructions 79744 128 hall_79616 checked_79744
  exact hall_79744

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
