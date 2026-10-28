module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_70656 : checkChunk context facts instructions 70656 128 = true := by decide +kernel

theorem checked_70784 : checkChunk context facts instructions 70784 128 = true := by decide +kernel

theorem checked_70912 : checkChunk context facts instructions 70912 128 = true := by decide +kernel

theorem checked_71040 : checkChunk context facts instructions 71040 128 = true := by decide +kernel

theorem checked_71168 : checkChunk context facts instructions 71168 128 = true := by decide +kernel

theorem checked_71296 : checkChunk context facts instructions 71296 128 = true := by decide +kernel

theorem checked_71424 : checkChunk context facts instructions 71424 128 = true := by decide +kernel

theorem checked_71552 : checkChunk context facts instructions 71552 128 = true := by decide +kernel

theorem holds_block_70656 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 70656 → Holds H g ρ (facts n)) :
    ∀ n, n < 71680 → Holds H g ρ (facts n) := by
  have hall_70656 := checkChunk_sound valid facts instructions 70656 128 prior checked_70656
  have hall_70784 := checkChunk_sound valid facts instructions 70784 128 hall_70656 checked_70784
  have hall_70912 := checkChunk_sound valid facts instructions 70912 128 hall_70784 checked_70912
  have hall_71040 := checkChunk_sound valid facts instructions 71040 128 hall_70912 checked_71040
  have hall_71168 := checkChunk_sound valid facts instructions 71168 128 hall_71040 checked_71168
  have hall_71296 := checkChunk_sound valid facts instructions 71296 128 hall_71168 checked_71296
  have hall_71424 := checkChunk_sound valid facts instructions 71424 128 hall_71296 checked_71424
  have hall_71552 := checkChunk_sound valid facts instructions 71552 128 hall_71424 checked_71552
  exact hall_71552

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
