module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_74752 : checkChunk context facts instructions 74752 128 = true := by decide +kernel

theorem checked_74880 : checkChunk context facts instructions 74880 128 = true := by decide +kernel

theorem checked_75008 : checkChunk context facts instructions 75008 128 = true := by decide +kernel

theorem checked_75136 : checkChunk context facts instructions 75136 128 = true := by decide +kernel

theorem checked_75264 : checkChunk context facts instructions 75264 128 = true := by decide +kernel

theorem checked_75392 : checkChunk context facts instructions 75392 128 = true := by decide +kernel

theorem checked_75520 : checkChunk context facts instructions 75520 128 = true := by decide +kernel

theorem checked_75648 : checkChunk context facts instructions 75648 128 = true := by decide +kernel

theorem holds_block_74752 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 74752 → Holds H g ρ (facts n)) :
    ∀ n, n < 75776 → Holds H g ρ (facts n) := by
  have hall_74752 := checkChunk_sound valid facts instructions 74752 128 prior checked_74752
  have hall_74880 := checkChunk_sound valid facts instructions 74880 128 hall_74752 checked_74880
  have hall_75008 := checkChunk_sound valid facts instructions 75008 128 hall_74880 checked_75008
  have hall_75136 := checkChunk_sound valid facts instructions 75136 128 hall_75008 checked_75136
  have hall_75264 := checkChunk_sound valid facts instructions 75264 128 hall_75136 checked_75264
  have hall_75392 := checkChunk_sound valid facts instructions 75392 128 hall_75264 checked_75392
  have hall_75520 := checkChunk_sound valid facts instructions 75520 128 hall_75392 checked_75520
  have hall_75648 := checkChunk_sound valid facts instructions 75648 128 hall_75520 checked_75648
  exact hall_75648

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
