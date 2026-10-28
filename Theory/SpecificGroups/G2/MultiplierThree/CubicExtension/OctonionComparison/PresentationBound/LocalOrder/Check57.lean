module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_58368 : checkChunk context facts instructions 58368 128 = true := by decide +kernel

theorem checked_58496 : checkChunk context facts instructions 58496 128 = true := by decide +kernel

theorem checked_58624 : checkChunk context facts instructions 58624 128 = true := by decide +kernel

theorem checked_58752 : checkChunk context facts instructions 58752 128 = true := by decide +kernel

theorem checked_58880 : checkChunk context facts instructions 58880 128 = true := by decide +kernel

theorem checked_59008 : checkChunk context facts instructions 59008 128 = true := by decide +kernel

theorem checked_59136 : checkChunk context facts instructions 59136 128 = true := by decide +kernel

theorem checked_59264 : checkChunk context facts instructions 59264 128 = true := by decide +kernel

theorem holds_block_58368 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 58368 → Holds H g ρ (facts n)) :
    ∀ n, n < 59392 → Holds H g ρ (facts n) := by
  have hall_58368 := checkChunk_sound valid facts instructions 58368 128 prior checked_58368
  have hall_58496 := checkChunk_sound valid facts instructions 58496 128 hall_58368 checked_58496
  have hall_58624 := checkChunk_sound valid facts instructions 58624 128 hall_58496 checked_58624
  have hall_58752 := checkChunk_sound valid facts instructions 58752 128 hall_58624 checked_58752
  have hall_58880 := checkChunk_sound valid facts instructions 58880 128 hall_58752 checked_58880
  have hall_59008 := checkChunk_sound valid facts instructions 59008 128 hall_58880 checked_59008
  have hall_59136 := checkChunk_sound valid facts instructions 59136 128 hall_59008 checked_59136
  have hall_59264 := checkChunk_sound valid facts instructions 59264 128 hall_59136 checked_59264
  exact hall_59264

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
