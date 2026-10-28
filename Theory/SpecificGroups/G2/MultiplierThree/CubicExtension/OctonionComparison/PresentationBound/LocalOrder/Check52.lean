module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_53248 : checkChunk context facts instructions 53248 128 = true := by decide +kernel

theorem checked_53376 : checkChunk context facts instructions 53376 128 = true := by decide +kernel

theorem checked_53504 : checkChunk context facts instructions 53504 128 = true := by decide +kernel

theorem checked_53632 : checkChunk context facts instructions 53632 128 = true := by decide +kernel

theorem checked_53760 : checkChunk context facts instructions 53760 128 = true := by decide +kernel

theorem checked_53888 : checkChunk context facts instructions 53888 128 = true := by decide +kernel

theorem checked_54016 : checkChunk context facts instructions 54016 128 = true := by decide +kernel

theorem checked_54144 : checkChunk context facts instructions 54144 128 = true := by decide +kernel

theorem holds_block_53248 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 53248 → Holds H g ρ (facts n)) :
    ∀ n, n < 54272 → Holds H g ρ (facts n) := by
  have hall_53248 := checkChunk_sound valid facts instructions 53248 128 prior checked_53248
  have hall_53376 := checkChunk_sound valid facts instructions 53376 128 hall_53248 checked_53376
  have hall_53504 := checkChunk_sound valid facts instructions 53504 128 hall_53376 checked_53504
  have hall_53632 := checkChunk_sound valid facts instructions 53632 128 hall_53504 checked_53632
  have hall_53760 := checkChunk_sound valid facts instructions 53760 128 hall_53632 checked_53760
  have hall_53888 := checkChunk_sound valid facts instructions 53888 128 hall_53760 checked_53888
  have hall_54016 := checkChunk_sound valid facts instructions 54016 128 hall_53888 checked_54016
  have hall_54144 := checkChunk_sound valid facts instructions 54144 128 hall_54016 checked_54144
  exact hall_54144

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
