module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_22528 : checkChunk context facts instructions 22528 128 = true := by decide +kernel

theorem checked_22656 : checkChunk context facts instructions 22656 128 = true := by decide +kernel

theorem checked_22784 : checkChunk context facts instructions 22784 128 = true := by decide +kernel

theorem checked_22912 : checkChunk context facts instructions 22912 128 = true := by decide +kernel

theorem checked_23040 : checkChunk context facts instructions 23040 128 = true := by decide +kernel

theorem checked_23168 : checkChunk context facts instructions 23168 128 = true := by decide +kernel

theorem checked_23296 : checkChunk context facts instructions 23296 128 = true := by decide +kernel

theorem checked_23424 : checkChunk context facts instructions 23424 128 = true := by decide +kernel

theorem holds_block_22528 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 22528 → Holds H g ρ (facts n)) :
    ∀ n, n < 23552 → Holds H g ρ (facts n) := by
  have hall_22528 := checkChunk_sound valid facts instructions 22528 128 prior checked_22528
  have hall_22656 := checkChunk_sound valid facts instructions 22656 128 hall_22528 checked_22656
  have hall_22784 := checkChunk_sound valid facts instructions 22784 128 hall_22656 checked_22784
  have hall_22912 := checkChunk_sound valid facts instructions 22912 128 hall_22784 checked_22912
  have hall_23040 := checkChunk_sound valid facts instructions 23040 128 hall_22912 checked_23040
  have hall_23168 := checkChunk_sound valid facts instructions 23168 128 hall_23040 checked_23168
  have hall_23296 := checkChunk_sound valid facts instructions 23296 128 hall_23168 checked_23296
  have hall_23424 := checkChunk_sound valid facts instructions 23424 128 hall_23296 checked_23424
  exact hall_23424

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
