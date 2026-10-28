module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_23552 : checkChunk context facts instructions 23552 128 = true := by decide +kernel

theorem checked_23680 : checkChunk context facts instructions 23680 128 = true := by decide +kernel

theorem checked_23808 : checkChunk context facts instructions 23808 128 = true := by decide +kernel

theorem checked_23936 : checkChunk context facts instructions 23936 128 = true := by decide +kernel

theorem checked_24064 : checkChunk context facts instructions 24064 128 = true := by decide +kernel

theorem checked_24192 : checkChunk context facts instructions 24192 128 = true := by decide +kernel

theorem checked_24320 : checkChunk context facts instructions 24320 128 = true := by decide +kernel

theorem checked_24448 : checkChunk context facts instructions 24448 128 = true := by decide +kernel

theorem holds_block_23552 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 23552 → Holds H g ρ (facts n)) :
    ∀ n, n < 24576 → Holds H g ρ (facts n) := by
  have hall_23552 := checkChunk_sound valid facts instructions 23552 128 prior checked_23552
  have hall_23680 := checkChunk_sound valid facts instructions 23680 128 hall_23552 checked_23680
  have hall_23808 := checkChunk_sound valid facts instructions 23808 128 hall_23680 checked_23808
  have hall_23936 := checkChunk_sound valid facts instructions 23936 128 hall_23808 checked_23936
  have hall_24064 := checkChunk_sound valid facts instructions 24064 128 hall_23936 checked_24064
  have hall_24192 := checkChunk_sound valid facts instructions 24192 128 hall_24064 checked_24192
  have hall_24320 := checkChunk_sound valid facts instructions 24320 128 hall_24192 checked_24320
  have hall_24448 := checkChunk_sound valid facts instructions 24448 128 hall_24320 checked_24448
  exact hall_24448

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
