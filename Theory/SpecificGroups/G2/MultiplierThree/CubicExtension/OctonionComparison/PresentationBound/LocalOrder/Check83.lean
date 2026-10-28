module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_84992 : checkChunk context facts instructions 84992 128 = true := by decide +kernel

theorem checked_85120 : checkChunk context facts instructions 85120 128 = true := by decide +kernel

theorem checked_85248 : checkChunk context facts instructions 85248 128 = true := by decide +kernel

theorem checked_85376 : checkChunk context facts instructions 85376 128 = true := by decide +kernel

theorem checked_85504 : checkChunk context facts instructions 85504 72 = true := by decide +kernel

theorem holds_block_84992 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 84992 → Holds H g ρ (facts n)) :
    ∀ n, n < 85576 → Holds H g ρ (facts n) := by
  have hall_84992 := checkChunk_sound valid facts instructions 84992 128 prior checked_84992
  have hall_85120 := checkChunk_sound valid facts instructions 85120 128 hall_84992 checked_85120
  have hall_85248 := checkChunk_sound valid facts instructions 85248 128 hall_85120 checked_85248
  have hall_85376 := checkChunk_sound valid facts instructions 85376 128 hall_85248 checked_85376
  have hall_85504 := checkChunk_sound valid facts instructions 85504 72 hall_85376 checked_85504
  exact hall_85504

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
