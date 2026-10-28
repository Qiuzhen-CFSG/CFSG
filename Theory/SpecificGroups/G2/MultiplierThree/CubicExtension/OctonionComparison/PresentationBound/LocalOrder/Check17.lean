module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_17408 : checkChunk context facts instructions 17408 128 = true := by decide +kernel

theorem checked_17536 : checkChunk context facts instructions 17536 128 = true := by decide +kernel

theorem checked_17664 : checkChunk context facts instructions 17664 128 = true := by decide +kernel

theorem checked_17792 : checkChunk context facts instructions 17792 128 = true := by decide +kernel

theorem checked_17920 : checkChunk context facts instructions 17920 128 = true := by decide +kernel

theorem checked_18048 : checkChunk context facts instructions 18048 128 = true := by decide +kernel

theorem checked_18176 : checkChunk context facts instructions 18176 128 = true := by decide +kernel

theorem checked_18304 : checkChunk context facts instructions 18304 128 = true := by decide +kernel

theorem holds_block_17408 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 17408 → Holds H g ρ (facts n)) :
    ∀ n, n < 18432 → Holds H g ρ (facts n) := by
  have hall_17408 := checkChunk_sound valid facts instructions 17408 128 prior checked_17408
  have hall_17536 := checkChunk_sound valid facts instructions 17536 128 hall_17408 checked_17536
  have hall_17664 := checkChunk_sound valid facts instructions 17664 128 hall_17536 checked_17664
  have hall_17792 := checkChunk_sound valid facts instructions 17792 128 hall_17664 checked_17792
  have hall_17920 := checkChunk_sound valid facts instructions 17920 128 hall_17792 checked_17920
  have hall_18048 := checkChunk_sound valid facts instructions 18048 128 hall_17920 checked_18048
  have hall_18176 := checkChunk_sound valid facts instructions 18176 128 hall_18048 checked_18176
  have hall_18304 := checkChunk_sound valid facts instructions 18304 128 hall_18176 checked_18304
  exact hall_18304

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
