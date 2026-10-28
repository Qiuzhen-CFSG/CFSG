module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_15360 : checkChunk context facts instructions 15360 128 = true := by decide +kernel

theorem checked_15488 : checkChunk context facts instructions 15488 128 = true := by decide +kernel

theorem checked_15616 : checkChunk context facts instructions 15616 128 = true := by decide +kernel

theorem checked_15744 : checkChunk context facts instructions 15744 128 = true := by decide +kernel

theorem checked_15872 : checkChunk context facts instructions 15872 128 = true := by decide +kernel

theorem checked_16000 : checkChunk context facts instructions 16000 128 = true := by decide +kernel

theorem checked_16128 : checkChunk context facts instructions 16128 128 = true := by decide +kernel

theorem checked_16256 : checkChunk context facts instructions 16256 128 = true := by decide +kernel

theorem holds_block_15360 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 15360 → Holds H g ρ (facts n)) :
    ∀ n, n < 16384 → Holds H g ρ (facts n) := by
  have hall_15360 := checkChunk_sound valid facts instructions 15360 128 prior checked_15360
  have hall_15488 := checkChunk_sound valid facts instructions 15488 128 hall_15360 checked_15488
  have hall_15616 := checkChunk_sound valid facts instructions 15616 128 hall_15488 checked_15616
  have hall_15744 := checkChunk_sound valid facts instructions 15744 128 hall_15616 checked_15744
  have hall_15872 := checkChunk_sound valid facts instructions 15872 128 hall_15744 checked_15872
  have hall_16000 := checkChunk_sound valid facts instructions 16000 128 hall_15872 checked_16000
  have hall_16128 := checkChunk_sound valid facts instructions 16128 128 hall_16000 checked_16128
  have hall_16256 := checkChunk_sound valid facts instructions 16256 128 hall_16128 checked_16256
  exact hall_16256

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
