module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_57344 : checkChunk context facts instructions 57344 128 = true := by decide +kernel

theorem checked_57472 : checkChunk context facts instructions 57472 128 = true := by decide +kernel

theorem checked_57600 : checkChunk context facts instructions 57600 128 = true := by decide +kernel

theorem checked_57728 : checkChunk context facts instructions 57728 128 = true := by decide +kernel

theorem checked_57856 : checkChunk context facts instructions 57856 128 = true := by decide +kernel

theorem checked_57984 : checkChunk context facts instructions 57984 128 = true := by decide +kernel

theorem checked_58112 : checkChunk context facts instructions 58112 128 = true := by decide +kernel

theorem checked_58240 : checkChunk context facts instructions 58240 128 = true := by decide +kernel

theorem holds_block_57344 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 57344 → Holds H g ρ (facts n)) :
    ∀ n, n < 58368 → Holds H g ρ (facts n) := by
  have hall_57344 := checkChunk_sound valid facts instructions 57344 128 prior checked_57344
  have hall_57472 := checkChunk_sound valid facts instructions 57472 128 hall_57344 checked_57472
  have hall_57600 := checkChunk_sound valid facts instructions 57600 128 hall_57472 checked_57600
  have hall_57728 := checkChunk_sound valid facts instructions 57728 128 hall_57600 checked_57728
  have hall_57856 := checkChunk_sound valid facts instructions 57856 128 hall_57728 checked_57856
  have hall_57984 := checkChunk_sound valid facts instructions 57984 128 hall_57856 checked_57984
  have hall_58112 := checkChunk_sound valid facts instructions 58112 128 hall_57984 checked_58112
  have hall_58240 := checkChunk_sound valid facts instructions 58240 128 hall_58112 checked_58240
  exact hall_58240

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
