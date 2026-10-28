module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_39936 : checkChunk context facts instructions 39936 128 = true := by decide +kernel

theorem checked_40064 : checkChunk context facts instructions 40064 128 = true := by decide +kernel

theorem checked_40192 : checkChunk context facts instructions 40192 128 = true := by decide +kernel

theorem checked_40320 : checkChunk context facts instructions 40320 128 = true := by decide +kernel

theorem checked_40448 : checkChunk context facts instructions 40448 128 = true := by decide +kernel

theorem checked_40576 : checkChunk context facts instructions 40576 128 = true := by decide +kernel

theorem checked_40704 : checkChunk context facts instructions 40704 128 = true := by decide +kernel

theorem checked_40832 : checkChunk context facts instructions 40832 128 = true := by decide +kernel

theorem holds_block_39936 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 39936 → Holds H g ρ (facts n)) :
    ∀ n, n < 40960 → Holds H g ρ (facts n) := by
  have hall_39936 := checkChunk_sound valid facts instructions 39936 128 prior checked_39936
  have hall_40064 := checkChunk_sound valid facts instructions 40064 128 hall_39936 checked_40064
  have hall_40192 := checkChunk_sound valid facts instructions 40192 128 hall_40064 checked_40192
  have hall_40320 := checkChunk_sound valid facts instructions 40320 128 hall_40192 checked_40320
  have hall_40448 := checkChunk_sound valid facts instructions 40448 128 hall_40320 checked_40448
  have hall_40576 := checkChunk_sound valid facts instructions 40576 128 hall_40448 checked_40576
  have hall_40704 := checkChunk_sound valid facts instructions 40704 128 hall_40576 checked_40704
  have hall_40832 := checkChunk_sound valid facts instructions 40832 128 hall_40704 checked_40832
  exact hall_40832

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
