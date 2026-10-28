module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_60416 : checkChunk context facts instructions 60416 128 = true := by decide +kernel

theorem checked_60544 : checkChunk context facts instructions 60544 128 = true := by decide +kernel

theorem checked_60672 : checkChunk context facts instructions 60672 128 = true := by decide +kernel

theorem checked_60800 : checkChunk context facts instructions 60800 128 = true := by decide +kernel

theorem checked_60928 : checkChunk context facts instructions 60928 128 = true := by decide +kernel

theorem checked_61056 : checkChunk context facts instructions 61056 128 = true := by decide +kernel

theorem checked_61184 : checkChunk context facts instructions 61184 128 = true := by decide +kernel

theorem checked_61312 : checkChunk context facts instructions 61312 128 = true := by decide +kernel

theorem holds_block_60416 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 60416 → Holds H g ρ (facts n)) :
    ∀ n, n < 61440 → Holds H g ρ (facts n) := by
  have hall_60416 := checkChunk_sound valid facts instructions 60416 128 prior checked_60416
  have hall_60544 := checkChunk_sound valid facts instructions 60544 128 hall_60416 checked_60544
  have hall_60672 := checkChunk_sound valid facts instructions 60672 128 hall_60544 checked_60672
  have hall_60800 := checkChunk_sound valid facts instructions 60800 128 hall_60672 checked_60800
  have hall_60928 := checkChunk_sound valid facts instructions 60928 128 hall_60800 checked_60928
  have hall_61056 := checkChunk_sound valid facts instructions 61056 128 hall_60928 checked_61056
  have hall_61184 := checkChunk_sound valid facts instructions 61184 128 hall_61056 checked_61184
  have hall_61312 := checkChunk_sound valid facts instructions 61312 128 hall_61184 checked_61312
  exact hall_61312

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
