module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_5120 : checkChunk context facts instructions 5120 128 = true := by decide +kernel

theorem checked_5248 : checkChunk context facts instructions 5248 128 = true := by decide +kernel

theorem checked_5376 : checkChunk context facts instructions 5376 128 = true := by decide +kernel

theorem checked_5504 : checkChunk context facts instructions 5504 128 = true := by decide +kernel

theorem checked_5632 : checkChunk context facts instructions 5632 128 = true := by decide +kernel

theorem checked_5760 : checkChunk context facts instructions 5760 128 = true := by decide +kernel

theorem checked_5888 : checkChunk context facts instructions 5888 128 = true := by decide +kernel

theorem checked_6016 : checkChunk context facts instructions 6016 128 = true := by decide +kernel

theorem holds_block_5120 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 5120 → Holds H g ρ (facts n)) :
    ∀ n, n < 6144 → Holds H g ρ (facts n) := by
  have hall_5120 := checkChunk_sound valid facts instructions 5120 128 prior checked_5120
  have hall_5248 := checkChunk_sound valid facts instructions 5248 128 hall_5120 checked_5248
  have hall_5376 := checkChunk_sound valid facts instructions 5376 128 hall_5248 checked_5376
  have hall_5504 := checkChunk_sound valid facts instructions 5504 128 hall_5376 checked_5504
  have hall_5632 := checkChunk_sound valid facts instructions 5632 128 hall_5504 checked_5632
  have hall_5760 := checkChunk_sound valid facts instructions 5760 128 hall_5632 checked_5760
  have hall_5888 := checkChunk_sound valid facts instructions 5888 128 hall_5760 checked_5888
  have hall_6016 := checkChunk_sound valid facts instructions 6016 128 hall_5888 checked_6016
  exact hall_6016

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
