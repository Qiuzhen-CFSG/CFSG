module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_38912 : checkChunk context facts instructions 38912 128 = true := by decide +kernel

theorem checked_39040 : checkChunk context facts instructions 39040 128 = true := by decide +kernel

theorem checked_39168 : checkChunk context facts instructions 39168 128 = true := by decide +kernel

theorem checked_39296 : checkChunk context facts instructions 39296 128 = true := by decide +kernel

theorem checked_39424 : checkChunk context facts instructions 39424 128 = true := by decide +kernel

theorem checked_39552 : checkChunk context facts instructions 39552 128 = true := by decide +kernel

theorem checked_39680 : checkChunk context facts instructions 39680 128 = true := by decide +kernel

theorem checked_39808 : checkChunk context facts instructions 39808 128 = true := by decide +kernel

theorem holds_block_38912 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 38912 → Holds H g ρ (facts n)) :
    ∀ n, n < 39936 → Holds H g ρ (facts n) := by
  have hall_38912 := checkChunk_sound valid facts instructions 38912 128 prior checked_38912
  have hall_39040 := checkChunk_sound valid facts instructions 39040 128 hall_38912 checked_39040
  have hall_39168 := checkChunk_sound valid facts instructions 39168 128 hall_39040 checked_39168
  have hall_39296 := checkChunk_sound valid facts instructions 39296 128 hall_39168 checked_39296
  have hall_39424 := checkChunk_sound valid facts instructions 39424 128 hall_39296 checked_39424
  have hall_39552 := checkChunk_sound valid facts instructions 39552 128 hall_39424 checked_39552
  have hall_39680 := checkChunk_sound valid facts instructions 39680 128 hall_39552 checked_39680
  have hall_39808 := checkChunk_sound valid facts instructions 39808 128 hall_39680 checked_39808
  exact hall_39808

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
