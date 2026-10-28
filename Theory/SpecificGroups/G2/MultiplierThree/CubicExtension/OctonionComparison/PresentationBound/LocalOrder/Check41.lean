module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_41984 : checkChunk context facts instructions 41984 128 = true := by decide +kernel

theorem checked_42112 : checkChunk context facts instructions 42112 128 = true := by decide +kernel

theorem checked_42240 : checkChunk context facts instructions 42240 128 = true := by decide +kernel

theorem checked_42368 : checkChunk context facts instructions 42368 128 = true := by decide +kernel

theorem checked_42496 : checkChunk context facts instructions 42496 128 = true := by decide +kernel

theorem checked_42624 : checkChunk context facts instructions 42624 128 = true := by decide +kernel

theorem checked_42752 : checkChunk context facts instructions 42752 128 = true := by decide +kernel

theorem checked_42880 : checkChunk context facts instructions 42880 128 = true := by decide +kernel

theorem holds_block_41984 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 41984 → Holds H g ρ (facts n)) :
    ∀ n, n < 43008 → Holds H g ρ (facts n) := by
  have hall_41984 := checkChunk_sound valid facts instructions 41984 128 prior checked_41984
  have hall_42112 := checkChunk_sound valid facts instructions 42112 128 hall_41984 checked_42112
  have hall_42240 := checkChunk_sound valid facts instructions 42240 128 hall_42112 checked_42240
  have hall_42368 := checkChunk_sound valid facts instructions 42368 128 hall_42240 checked_42368
  have hall_42496 := checkChunk_sound valid facts instructions 42496 128 hall_42368 checked_42496
  have hall_42624 := checkChunk_sound valid facts instructions 42624 128 hall_42496 checked_42624
  have hall_42752 := checkChunk_sound valid facts instructions 42752 128 hall_42624 checked_42752
  have hall_42880 := checkChunk_sound valid facts instructions 42880 128 hall_42752 checked_42880
  exact hall_42880

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
