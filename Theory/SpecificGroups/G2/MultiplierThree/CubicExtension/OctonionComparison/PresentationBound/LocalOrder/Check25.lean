module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_25600 : checkChunk context facts instructions 25600 128 = true := by decide +kernel

theorem checked_25728 : checkChunk context facts instructions 25728 128 = true := by decide +kernel

theorem checked_25856 : checkChunk context facts instructions 25856 128 = true := by decide +kernel

theorem checked_25984 : checkChunk context facts instructions 25984 128 = true := by decide +kernel

theorem checked_26112 : checkChunk context facts instructions 26112 128 = true := by decide +kernel

theorem checked_26240 : checkChunk context facts instructions 26240 128 = true := by decide +kernel

theorem checked_26368 : checkChunk context facts instructions 26368 128 = true := by decide +kernel

theorem checked_26496 : checkChunk context facts instructions 26496 128 = true := by decide +kernel

theorem holds_block_25600 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 25600 → Holds H g ρ (facts n)) :
    ∀ n, n < 26624 → Holds H g ρ (facts n) := by
  have hall_25600 := checkChunk_sound valid facts instructions 25600 128 prior checked_25600
  have hall_25728 := checkChunk_sound valid facts instructions 25728 128 hall_25600 checked_25728
  have hall_25856 := checkChunk_sound valid facts instructions 25856 128 hall_25728 checked_25856
  have hall_25984 := checkChunk_sound valid facts instructions 25984 128 hall_25856 checked_25984
  have hall_26112 := checkChunk_sound valid facts instructions 26112 128 hall_25984 checked_26112
  have hall_26240 := checkChunk_sound valid facts instructions 26240 128 hall_26112 checked_26240
  have hall_26368 := checkChunk_sound valid facts instructions 26368 128 hall_26240 checked_26368
  have hall_26496 := checkChunk_sound valid facts instructions 26496 128 hall_26368 checked_26496
  exact hall_26496

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
