module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_81920 : checkChunk context facts instructions 81920 128 = true := by decide +kernel

theorem checked_82048 : checkChunk context facts instructions 82048 128 = true := by decide +kernel

theorem checked_82176 : checkChunk context facts instructions 82176 128 = true := by decide +kernel

theorem checked_82304 : checkChunk context facts instructions 82304 128 = true := by decide +kernel

theorem checked_82432 : checkChunk context facts instructions 82432 128 = true := by decide +kernel

theorem checked_82560 : checkChunk context facts instructions 82560 128 = true := by decide +kernel

theorem checked_82688 : checkChunk context facts instructions 82688 128 = true := by decide +kernel

theorem checked_82816 : checkChunk context facts instructions 82816 128 = true := by decide +kernel

theorem holds_block_81920 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 81920 → Holds H g ρ (facts n)) :
    ∀ n, n < 82944 → Holds H g ρ (facts n) := by
  have hall_81920 := checkChunk_sound valid facts instructions 81920 128 prior checked_81920
  have hall_82048 := checkChunk_sound valid facts instructions 82048 128 hall_81920 checked_82048
  have hall_82176 := checkChunk_sound valid facts instructions 82176 128 hall_82048 checked_82176
  have hall_82304 := checkChunk_sound valid facts instructions 82304 128 hall_82176 checked_82304
  have hall_82432 := checkChunk_sound valid facts instructions 82432 128 hall_82304 checked_82432
  have hall_82560 := checkChunk_sound valid facts instructions 82560 128 hall_82432 checked_82560
  have hall_82688 := checkChunk_sound valid facts instructions 82688 128 hall_82560 checked_82688
  have hall_82816 := checkChunk_sound valid facts instructions 82816 128 hall_82688 checked_82816
  exact hall_82816

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
