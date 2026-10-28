module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_69632 : checkChunk context facts instructions 69632 128 = true := by decide +kernel

theorem checked_69760 : checkChunk context facts instructions 69760 128 = true := by decide +kernel

theorem checked_69888 : checkChunk context facts instructions 69888 128 = true := by decide +kernel

theorem checked_70016 : checkChunk context facts instructions 70016 128 = true := by decide +kernel

theorem checked_70144 : checkChunk context facts instructions 70144 128 = true := by decide +kernel

theorem checked_70272 : checkChunk context facts instructions 70272 128 = true := by decide +kernel

theorem checked_70400 : checkChunk context facts instructions 70400 128 = true := by decide +kernel

theorem checked_70528 : checkChunk context facts instructions 70528 128 = true := by decide +kernel

theorem holds_block_69632 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 69632 → Holds H g ρ (facts n)) :
    ∀ n, n < 70656 → Holds H g ρ (facts n) := by
  have hall_69632 := checkChunk_sound valid facts instructions 69632 128 prior checked_69632
  have hall_69760 := checkChunk_sound valid facts instructions 69760 128 hall_69632 checked_69760
  have hall_69888 := checkChunk_sound valid facts instructions 69888 128 hall_69760 checked_69888
  have hall_70016 := checkChunk_sound valid facts instructions 70016 128 hall_69888 checked_70016
  have hall_70144 := checkChunk_sound valid facts instructions 70144 128 hall_70016 checked_70144
  have hall_70272 := checkChunk_sound valid facts instructions 70272 128 hall_70144 checked_70272
  have hall_70400 := checkChunk_sound valid facts instructions 70400 128 hall_70272 checked_70400
  have hall_70528 := checkChunk_sound valid facts instructions 70528 128 hall_70400 checked_70528
  exact hall_70528

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
