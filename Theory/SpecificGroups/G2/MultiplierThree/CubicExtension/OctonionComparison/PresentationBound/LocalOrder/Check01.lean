module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_1024 : checkChunk context facts instructions 1024 128 = true := by decide +kernel

theorem checked_1152 : checkChunk context facts instructions 1152 128 = true := by decide +kernel

theorem checked_1280 : checkChunk context facts instructions 1280 128 = true := by decide +kernel

theorem checked_1408 : checkChunk context facts instructions 1408 128 = true := by decide +kernel

theorem checked_1536 : checkChunk context facts instructions 1536 128 = true := by decide +kernel

theorem checked_1664 : checkChunk context facts instructions 1664 128 = true := by decide +kernel

theorem checked_1792 : checkChunk context facts instructions 1792 128 = true := by decide +kernel

theorem checked_1920 : checkChunk context facts instructions 1920 128 = true := by decide +kernel

theorem holds_block_1024 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 1024 → Holds H g ρ (facts n)) :
    ∀ n, n < 2048 → Holds H g ρ (facts n) := by
  have hall_1024 := checkChunk_sound valid facts instructions 1024 128 prior checked_1024
  have hall_1152 := checkChunk_sound valid facts instructions 1152 128 hall_1024 checked_1152
  have hall_1280 := checkChunk_sound valid facts instructions 1280 128 hall_1152 checked_1280
  have hall_1408 := checkChunk_sound valid facts instructions 1408 128 hall_1280 checked_1408
  have hall_1536 := checkChunk_sound valid facts instructions 1536 128 hall_1408 checked_1536
  have hall_1664 := checkChunk_sound valid facts instructions 1664 128 hall_1536 checked_1664
  have hall_1792 := checkChunk_sound valid facts instructions 1792 128 hall_1664 checked_1792
  have hall_1920 := checkChunk_sound valid facts instructions 1920 128 hall_1792 checked_1920
  exact hall_1920

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
