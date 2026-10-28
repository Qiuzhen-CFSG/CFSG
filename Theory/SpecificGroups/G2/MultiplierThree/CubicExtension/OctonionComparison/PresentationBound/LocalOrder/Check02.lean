module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_2048 : checkChunk context facts instructions 2048 128 = true := by decide +kernel

theorem checked_2176 : checkChunk context facts instructions 2176 128 = true := by decide +kernel

theorem checked_2304 : checkChunk context facts instructions 2304 128 = true := by decide +kernel

theorem checked_2432 : checkChunk context facts instructions 2432 128 = true := by decide +kernel

theorem checked_2560 : checkChunk context facts instructions 2560 128 = true := by decide +kernel

theorem checked_2688 : checkChunk context facts instructions 2688 128 = true := by decide +kernel

theorem checked_2816 : checkChunk context facts instructions 2816 128 = true := by decide +kernel

theorem checked_2944 : checkChunk context facts instructions 2944 128 = true := by decide +kernel

theorem holds_block_2048 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 2048 → Holds H g ρ (facts n)) :
    ∀ n, n < 3072 → Holds H g ρ (facts n) := by
  have hall_2048 := checkChunk_sound valid facts instructions 2048 128 prior checked_2048
  have hall_2176 := checkChunk_sound valid facts instructions 2176 128 hall_2048 checked_2176
  have hall_2304 := checkChunk_sound valid facts instructions 2304 128 hall_2176 checked_2304
  have hall_2432 := checkChunk_sound valid facts instructions 2432 128 hall_2304 checked_2432
  have hall_2560 := checkChunk_sound valid facts instructions 2560 128 hall_2432 checked_2560
  have hall_2688 := checkChunk_sound valid facts instructions 2688 128 hall_2560 checked_2688
  have hall_2816 := checkChunk_sound valid facts instructions 2816 128 hall_2688 checked_2816
  have hall_2944 := checkChunk_sound valid facts instructions 2944 128 hall_2816 checked_2944
  exact hall_2944

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
