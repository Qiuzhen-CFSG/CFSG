module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_51200 : checkChunk context facts instructions 51200 128 = true := by decide +kernel

theorem checked_51328 : checkChunk context facts instructions 51328 128 = true := by decide +kernel

theorem checked_51456 : checkChunk context facts instructions 51456 128 = true := by decide +kernel

theorem checked_51584 : checkChunk context facts instructions 51584 128 = true := by decide +kernel

theorem checked_51712 : checkChunk context facts instructions 51712 128 = true := by decide +kernel

theorem checked_51840 : checkChunk context facts instructions 51840 128 = true := by decide +kernel

theorem checked_51968 : checkChunk context facts instructions 51968 128 = true := by decide +kernel

theorem checked_52096 : checkChunk context facts instructions 52096 128 = true := by decide +kernel

theorem holds_block_51200 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 51200 → Holds H g ρ (facts n)) :
    ∀ n, n < 52224 → Holds H g ρ (facts n) := by
  have hall_51200 := checkChunk_sound valid facts instructions 51200 128 prior checked_51200
  have hall_51328 := checkChunk_sound valid facts instructions 51328 128 hall_51200 checked_51328
  have hall_51456 := checkChunk_sound valid facts instructions 51456 128 hall_51328 checked_51456
  have hall_51584 := checkChunk_sound valid facts instructions 51584 128 hall_51456 checked_51584
  have hall_51712 := checkChunk_sound valid facts instructions 51712 128 hall_51584 checked_51712
  have hall_51840 := checkChunk_sound valid facts instructions 51840 128 hall_51712 checked_51840
  have hall_51968 := checkChunk_sound valid facts instructions 51968 128 hall_51840 checked_51968
  have hall_52096 := checkChunk_sound valid facts instructions 52096 128 hall_51968 checked_52096
  exact hall_52096

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
