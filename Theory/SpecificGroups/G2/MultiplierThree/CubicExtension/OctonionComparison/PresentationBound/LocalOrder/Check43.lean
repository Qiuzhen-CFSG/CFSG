module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_44032 : checkChunk context facts instructions 44032 128 = true := by decide +kernel

theorem checked_44160 : checkChunk context facts instructions 44160 128 = true := by decide +kernel

theorem checked_44288 : checkChunk context facts instructions 44288 128 = true := by decide +kernel

theorem checked_44416 : checkChunk context facts instructions 44416 128 = true := by decide +kernel

theorem checked_44544 : checkChunk context facts instructions 44544 128 = true := by decide +kernel

theorem checked_44672 : checkChunk context facts instructions 44672 128 = true := by decide +kernel

theorem checked_44800 : checkChunk context facts instructions 44800 128 = true := by decide +kernel

theorem checked_44928 : checkChunk context facts instructions 44928 128 = true := by decide +kernel

theorem holds_block_44032 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 44032 → Holds H g ρ (facts n)) :
    ∀ n, n < 45056 → Holds H g ρ (facts n) := by
  have hall_44032 := checkChunk_sound valid facts instructions 44032 128 prior checked_44032
  have hall_44160 := checkChunk_sound valid facts instructions 44160 128 hall_44032 checked_44160
  have hall_44288 := checkChunk_sound valid facts instructions 44288 128 hall_44160 checked_44288
  have hall_44416 := checkChunk_sound valid facts instructions 44416 128 hall_44288 checked_44416
  have hall_44544 := checkChunk_sound valid facts instructions 44544 128 hall_44416 checked_44544
  have hall_44672 := checkChunk_sound valid facts instructions 44672 128 hall_44544 checked_44672
  have hall_44800 := checkChunk_sound valid facts instructions 44800 128 hall_44672 checked_44800
  have hall_44928 := checkChunk_sound valid facts instructions 44928 128 hall_44800 checked_44928
  exact hall_44928

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
