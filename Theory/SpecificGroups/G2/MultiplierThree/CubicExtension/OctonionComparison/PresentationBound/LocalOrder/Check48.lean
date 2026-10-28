module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_49152 : checkChunk context facts instructions 49152 128 = true := by decide +kernel

theorem checked_49280 : checkChunk context facts instructions 49280 128 = true := by decide +kernel

theorem checked_49408 : checkChunk context facts instructions 49408 128 = true := by decide +kernel

theorem checked_49536 : checkChunk context facts instructions 49536 128 = true := by decide +kernel

theorem checked_49664 : checkChunk context facts instructions 49664 128 = true := by decide +kernel

theorem checked_49792 : checkChunk context facts instructions 49792 128 = true := by decide +kernel

theorem checked_49920 : checkChunk context facts instructions 49920 128 = true := by decide +kernel

theorem checked_50048 : checkChunk context facts instructions 50048 128 = true := by decide +kernel

theorem holds_block_49152 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 49152 → Holds H g ρ (facts n)) :
    ∀ n, n < 50176 → Holds H g ρ (facts n) := by
  have hall_49152 := checkChunk_sound valid facts instructions 49152 128 prior checked_49152
  have hall_49280 := checkChunk_sound valid facts instructions 49280 128 hall_49152 checked_49280
  have hall_49408 := checkChunk_sound valid facts instructions 49408 128 hall_49280 checked_49408
  have hall_49536 := checkChunk_sound valid facts instructions 49536 128 hall_49408 checked_49536
  have hall_49664 := checkChunk_sound valid facts instructions 49664 128 hall_49536 checked_49664
  have hall_49792 := checkChunk_sound valid facts instructions 49792 128 hall_49664 checked_49792
  have hall_49920 := checkChunk_sound valid facts instructions 49920 128 hall_49792 checked_49920
  have hall_50048 := checkChunk_sound valid facts instructions 50048 128 hall_49920 checked_50048
  exact hall_50048

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
