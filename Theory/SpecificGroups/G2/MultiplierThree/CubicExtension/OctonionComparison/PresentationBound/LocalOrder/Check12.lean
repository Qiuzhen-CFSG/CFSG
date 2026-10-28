module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_12288 : checkChunk context facts instructions 12288 128 = true := by decide +kernel

theorem checked_12416 : checkChunk context facts instructions 12416 128 = true := by decide +kernel

theorem checked_12544 : checkChunk context facts instructions 12544 128 = true := by decide +kernel

theorem checked_12672 : checkChunk context facts instructions 12672 128 = true := by decide +kernel

theorem checked_12800 : checkChunk context facts instructions 12800 128 = true := by decide +kernel

theorem checked_12928 : checkChunk context facts instructions 12928 128 = true := by decide +kernel

theorem checked_13056 : checkChunk context facts instructions 13056 128 = true := by decide +kernel

theorem checked_13184 : checkChunk context facts instructions 13184 128 = true := by decide +kernel

theorem holds_block_12288 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 12288 → Holds H g ρ (facts n)) :
    ∀ n, n < 13312 → Holds H g ρ (facts n) := by
  have hall_12288 := checkChunk_sound valid facts instructions 12288 128 prior checked_12288
  have hall_12416 := checkChunk_sound valid facts instructions 12416 128 hall_12288 checked_12416
  have hall_12544 := checkChunk_sound valid facts instructions 12544 128 hall_12416 checked_12544
  have hall_12672 := checkChunk_sound valid facts instructions 12672 128 hall_12544 checked_12672
  have hall_12800 := checkChunk_sound valid facts instructions 12800 128 hall_12672 checked_12800
  have hall_12928 := checkChunk_sound valid facts instructions 12928 128 hall_12800 checked_12928
  have hall_13056 := checkChunk_sound valid facts instructions 13056 128 hall_12928 checked_13056
  have hall_13184 := checkChunk_sound valid facts instructions 13184 128 hall_13056 checked_13184
  exact hall_13184

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
