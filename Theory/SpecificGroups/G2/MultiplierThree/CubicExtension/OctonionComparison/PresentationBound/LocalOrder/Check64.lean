module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_65536 : checkChunk context facts instructions 65536 128 = true := by decide +kernel

theorem checked_65664 : checkChunk context facts instructions 65664 128 = true := by decide +kernel

theorem checked_65792 : checkChunk context facts instructions 65792 128 = true := by decide +kernel

theorem checked_65920 : checkChunk context facts instructions 65920 128 = true := by decide +kernel

theorem checked_66048 : checkChunk context facts instructions 66048 128 = true := by decide +kernel

theorem checked_66176 : checkChunk context facts instructions 66176 128 = true := by decide +kernel

theorem checked_66304 : checkChunk context facts instructions 66304 128 = true := by decide +kernel

theorem checked_66432 : checkChunk context facts instructions 66432 128 = true := by decide +kernel

theorem holds_block_65536 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 65536 → Holds H g ρ (facts n)) :
    ∀ n, n < 66560 → Holds H g ρ (facts n) := by
  have hall_65536 := checkChunk_sound valid facts instructions 65536 128 prior checked_65536
  have hall_65664 := checkChunk_sound valid facts instructions 65664 128 hall_65536 checked_65664
  have hall_65792 := checkChunk_sound valid facts instructions 65792 128 hall_65664 checked_65792
  have hall_65920 := checkChunk_sound valid facts instructions 65920 128 hall_65792 checked_65920
  have hall_66048 := checkChunk_sound valid facts instructions 66048 128 hall_65920 checked_66048
  have hall_66176 := checkChunk_sound valid facts instructions 66176 128 hall_66048 checked_66176
  have hall_66304 := checkChunk_sound valid facts instructions 66304 128 hall_66176 checked_66304
  have hall_66432 := checkChunk_sound valid facts instructions 66432 128 hall_66304 checked_66432
  exact hall_66432

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
