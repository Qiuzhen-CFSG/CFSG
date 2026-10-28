module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_62464 : checkChunk context facts instructions 62464 128 = true := by decide +kernel

theorem checked_62592 : checkChunk context facts instructions 62592 128 = true := by decide +kernel

theorem checked_62720 : checkChunk context facts instructions 62720 128 = true := by decide +kernel

theorem checked_62848 : checkChunk context facts instructions 62848 128 = true := by decide +kernel

theorem checked_62976 : checkChunk context facts instructions 62976 128 = true := by decide +kernel

theorem checked_63104 : checkChunk context facts instructions 63104 128 = true := by decide +kernel

theorem checked_63232 : checkChunk context facts instructions 63232 128 = true := by decide +kernel

theorem checked_63360 : checkChunk context facts instructions 63360 128 = true := by decide +kernel

theorem holds_block_62464 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 62464 → Holds H g ρ (facts n)) :
    ∀ n, n < 63488 → Holds H g ρ (facts n) := by
  have hall_62464 := checkChunk_sound valid facts instructions 62464 128 prior checked_62464
  have hall_62592 := checkChunk_sound valid facts instructions 62592 128 hall_62464 checked_62592
  have hall_62720 := checkChunk_sound valid facts instructions 62720 128 hall_62592 checked_62720
  have hall_62848 := checkChunk_sound valid facts instructions 62848 128 hall_62720 checked_62848
  have hall_62976 := checkChunk_sound valid facts instructions 62976 128 hall_62848 checked_62976
  have hall_63104 := checkChunk_sound valid facts instructions 63104 128 hall_62976 checked_63104
  have hall_63232 := checkChunk_sound valid facts instructions 63232 128 hall_63104 checked_63232
  have hall_63360 := checkChunk_sound valid facts instructions 63360 128 hall_63232 checked_63360
  exact hall_63360

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
