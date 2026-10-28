module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_54272 : checkChunk context facts instructions 54272 128 = true := by decide +kernel

theorem checked_54400 : checkChunk context facts instructions 54400 128 = true := by decide +kernel

theorem checked_54528 : checkChunk context facts instructions 54528 128 = true := by decide +kernel

theorem checked_54656 : checkChunk context facts instructions 54656 128 = true := by decide +kernel

theorem checked_54784 : checkChunk context facts instructions 54784 128 = true := by decide +kernel

theorem checked_54912 : checkChunk context facts instructions 54912 128 = true := by decide +kernel

theorem checked_55040 : checkChunk context facts instructions 55040 128 = true := by decide +kernel

theorem checked_55168 : checkChunk context facts instructions 55168 128 = true := by decide +kernel

theorem holds_block_54272 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 54272 → Holds H g ρ (facts n)) :
    ∀ n, n < 55296 → Holds H g ρ (facts n) := by
  have hall_54272 := checkChunk_sound valid facts instructions 54272 128 prior checked_54272
  have hall_54400 := checkChunk_sound valid facts instructions 54400 128 hall_54272 checked_54400
  have hall_54528 := checkChunk_sound valid facts instructions 54528 128 hall_54400 checked_54528
  have hall_54656 := checkChunk_sound valid facts instructions 54656 128 hall_54528 checked_54656
  have hall_54784 := checkChunk_sound valid facts instructions 54784 128 hall_54656 checked_54784
  have hall_54912 := checkChunk_sound valid facts instructions 54912 128 hall_54784 checked_54912
  have hall_55040 := checkChunk_sound valid facts instructions 55040 128 hall_54912 checked_55040
  have hall_55168 := checkChunk_sound valid facts instructions 55168 128 hall_55040 checked_55168
  exact hall_55168

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
