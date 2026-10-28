module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_73728 : checkChunk context facts instructions 73728 128 = true := by decide +kernel

theorem checked_73856 : checkChunk context facts instructions 73856 128 = true := by decide +kernel

theorem checked_73984 : checkChunk context facts instructions 73984 128 = true := by decide +kernel

theorem checked_74112 : checkChunk context facts instructions 74112 128 = true := by decide +kernel

theorem checked_74240 : checkChunk context facts instructions 74240 128 = true := by decide +kernel

theorem checked_74368 : checkChunk context facts instructions 74368 128 = true := by decide +kernel

theorem checked_74496 : checkChunk context facts instructions 74496 128 = true := by decide +kernel

theorem checked_74624 : checkChunk context facts instructions 74624 128 = true := by decide +kernel

theorem holds_block_73728 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 73728 → Holds H g ρ (facts n)) :
    ∀ n, n < 74752 → Holds H g ρ (facts n) := by
  have hall_73728 := checkChunk_sound valid facts instructions 73728 128 prior checked_73728
  have hall_73856 := checkChunk_sound valid facts instructions 73856 128 hall_73728 checked_73856
  have hall_73984 := checkChunk_sound valid facts instructions 73984 128 hall_73856 checked_73984
  have hall_74112 := checkChunk_sound valid facts instructions 74112 128 hall_73984 checked_74112
  have hall_74240 := checkChunk_sound valid facts instructions 74240 128 hall_74112 checked_74240
  have hall_74368 := checkChunk_sound valid facts instructions 74368 128 hall_74240 checked_74368
  have hall_74496 := checkChunk_sound valid facts instructions 74496 128 hall_74368 checked_74496
  have hall_74624 := checkChunk_sound valid facts instructions 74624 128 hall_74496 checked_74624
  exact hall_74624

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
