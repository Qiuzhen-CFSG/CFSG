module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_33792 : checkChunk context facts instructions 33792 128 = true := by decide +kernel

theorem checked_33920 : checkChunk context facts instructions 33920 128 = true := by decide +kernel

theorem checked_34048 : checkChunk context facts instructions 34048 128 = true := by decide +kernel

theorem checked_34176 : checkChunk context facts instructions 34176 128 = true := by decide +kernel

theorem checked_34304 : checkChunk context facts instructions 34304 128 = true := by decide +kernel

theorem checked_34432 : checkChunk context facts instructions 34432 128 = true := by decide +kernel

theorem checked_34560 : checkChunk context facts instructions 34560 128 = true := by decide +kernel

theorem checked_34688 : checkChunk context facts instructions 34688 128 = true := by decide +kernel

theorem holds_block_33792 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 33792 → Holds H g ρ (facts n)) :
    ∀ n, n < 34816 → Holds H g ρ (facts n) := by
  have hall_33792 := checkChunk_sound valid facts instructions 33792 128 prior checked_33792
  have hall_33920 := checkChunk_sound valid facts instructions 33920 128 hall_33792 checked_33920
  have hall_34048 := checkChunk_sound valid facts instructions 34048 128 hall_33920 checked_34048
  have hall_34176 := checkChunk_sound valid facts instructions 34176 128 hall_34048 checked_34176
  have hall_34304 := checkChunk_sound valid facts instructions 34304 128 hall_34176 checked_34304
  have hall_34432 := checkChunk_sound valid facts instructions 34432 128 hall_34304 checked_34432
  have hall_34560 := checkChunk_sound valid facts instructions 34560 128 hall_34432 checked_34560
  have hall_34688 := checkChunk_sound valid facts instructions 34688 128 hall_34560 checked_34688
  exact hall_34688

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
