module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_66560 : checkChunk context facts instructions 66560 128 = true := by decide +kernel

theorem checked_66688 : checkChunk context facts instructions 66688 128 = true := by decide +kernel

theorem checked_66816 : checkChunk context facts instructions 66816 128 = true := by decide +kernel

theorem checked_66944 : checkChunk context facts instructions 66944 128 = true := by decide +kernel

theorem checked_67072 : checkChunk context facts instructions 67072 128 = true := by decide +kernel

theorem checked_67200 : checkChunk context facts instructions 67200 128 = true := by decide +kernel

theorem checked_67328 : checkChunk context facts instructions 67328 128 = true := by decide +kernel

theorem checked_67456 : checkChunk context facts instructions 67456 128 = true := by decide +kernel

theorem holds_block_66560 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 66560 → Holds H g ρ (facts n)) :
    ∀ n, n < 67584 → Holds H g ρ (facts n) := by
  have hall_66560 := checkChunk_sound valid facts instructions 66560 128 prior checked_66560
  have hall_66688 := checkChunk_sound valid facts instructions 66688 128 hall_66560 checked_66688
  have hall_66816 := checkChunk_sound valid facts instructions 66816 128 hall_66688 checked_66816
  have hall_66944 := checkChunk_sound valid facts instructions 66944 128 hall_66816 checked_66944
  have hall_67072 := checkChunk_sound valid facts instructions 67072 128 hall_66944 checked_67072
  have hall_67200 := checkChunk_sound valid facts instructions 67200 128 hall_67072 checked_67200
  have hall_67328 := checkChunk_sound valid facts instructions 67328 128 hall_67200 checked_67328
  have hall_67456 := checkChunk_sound valid facts instructions 67456 128 hall_67328 checked_67456
  exact hall_67456

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
