module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_50176 : checkChunk context facts instructions 50176 128 = true := by decide +kernel

theorem checked_50304 : checkChunk context facts instructions 50304 128 = true := by decide +kernel

theorem checked_50432 : checkChunk context facts instructions 50432 128 = true := by decide +kernel

theorem checked_50560 : checkChunk context facts instructions 50560 128 = true := by decide +kernel

theorem checked_50688 : checkChunk context facts instructions 50688 128 = true := by decide +kernel

theorem checked_50816 : checkChunk context facts instructions 50816 128 = true := by decide +kernel

theorem checked_50944 : checkChunk context facts instructions 50944 128 = true := by decide +kernel

theorem checked_51072 : checkChunk context facts instructions 51072 128 = true := by decide +kernel

theorem holds_block_50176 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 50176 → Holds H g ρ (facts n)) :
    ∀ n, n < 51200 → Holds H g ρ (facts n) := by
  have hall_50176 := checkChunk_sound valid facts instructions 50176 128 prior checked_50176
  have hall_50304 := checkChunk_sound valid facts instructions 50304 128 hall_50176 checked_50304
  have hall_50432 := checkChunk_sound valid facts instructions 50432 128 hall_50304 checked_50432
  have hall_50560 := checkChunk_sound valid facts instructions 50560 128 hall_50432 checked_50560
  have hall_50688 := checkChunk_sound valid facts instructions 50688 128 hall_50560 checked_50688
  have hall_50816 := checkChunk_sound valid facts instructions 50816 128 hall_50688 checked_50816
  have hall_50944 := checkChunk_sound valid facts instructions 50944 128 hall_50816 checked_50944
  have hall_51072 := checkChunk_sound valid facts instructions 51072 128 hall_50944 checked_51072
  exact hall_51072

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
