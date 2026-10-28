module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_61440 : checkChunk context facts instructions 61440 128 = true := by decide +kernel

theorem checked_61568 : checkChunk context facts instructions 61568 128 = true := by decide +kernel

theorem checked_61696 : checkChunk context facts instructions 61696 128 = true := by decide +kernel

theorem checked_61824 : checkChunk context facts instructions 61824 128 = true := by decide +kernel

theorem checked_61952 : checkChunk context facts instructions 61952 128 = true := by decide +kernel

theorem checked_62080 : checkChunk context facts instructions 62080 128 = true := by decide +kernel

theorem checked_62208 : checkChunk context facts instructions 62208 128 = true := by decide +kernel

theorem checked_62336 : checkChunk context facts instructions 62336 128 = true := by decide +kernel

theorem holds_block_61440 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 61440 → Holds H g ρ (facts n)) :
    ∀ n, n < 62464 → Holds H g ρ (facts n) := by
  have hall_61440 := checkChunk_sound valid facts instructions 61440 128 prior checked_61440
  have hall_61568 := checkChunk_sound valid facts instructions 61568 128 hall_61440 checked_61568
  have hall_61696 := checkChunk_sound valid facts instructions 61696 128 hall_61568 checked_61696
  have hall_61824 := checkChunk_sound valid facts instructions 61824 128 hall_61696 checked_61824
  have hall_61952 := checkChunk_sound valid facts instructions 61952 128 hall_61824 checked_61952
  have hall_62080 := checkChunk_sound valid facts instructions 62080 128 hall_61952 checked_62080
  have hall_62208 := checkChunk_sound valid facts instructions 62208 128 hall_62080 checked_62208
  have hall_62336 := checkChunk_sound valid facts instructions 62336 128 hall_62208 checked_62336
  exact hall_62336

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
