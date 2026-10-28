module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_59392 : checkChunk context facts instructions 59392 128 = true := by decide +kernel

theorem checked_59520 : checkChunk context facts instructions 59520 128 = true := by decide +kernel

theorem checked_59648 : checkChunk context facts instructions 59648 128 = true := by decide +kernel

theorem checked_59776 : checkChunk context facts instructions 59776 128 = true := by decide +kernel

theorem checked_59904 : checkChunk context facts instructions 59904 128 = true := by decide +kernel

theorem checked_60032 : checkChunk context facts instructions 60032 128 = true := by decide +kernel

theorem checked_60160 : checkChunk context facts instructions 60160 128 = true := by decide +kernel

theorem checked_60288 : checkChunk context facts instructions 60288 128 = true := by decide +kernel

theorem holds_block_59392 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 59392 → Holds H g ρ (facts n)) :
    ∀ n, n < 60416 → Holds H g ρ (facts n) := by
  have hall_59392 := checkChunk_sound valid facts instructions 59392 128 prior checked_59392
  have hall_59520 := checkChunk_sound valid facts instructions 59520 128 hall_59392 checked_59520
  have hall_59648 := checkChunk_sound valid facts instructions 59648 128 hall_59520 checked_59648
  have hall_59776 := checkChunk_sound valid facts instructions 59776 128 hall_59648 checked_59776
  have hall_59904 := checkChunk_sound valid facts instructions 59904 128 hall_59776 checked_59904
  have hall_60032 := checkChunk_sound valid facts instructions 60032 128 hall_59904 checked_60032
  have hall_60160 := checkChunk_sound valid facts instructions 60160 128 hall_60032 checked_60160
  have hall_60288 := checkChunk_sound valid facts instructions 60288 128 hall_60160 checked_60288
  exact hall_60288

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
