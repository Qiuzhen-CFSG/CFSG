module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_20480 : checkChunk context facts instructions 20480 128 = true := by decide +kernel

theorem checked_20608 : checkChunk context facts instructions 20608 128 = true := by decide +kernel

theorem checked_20736 : checkChunk context facts instructions 20736 128 = true := by decide +kernel

theorem checked_20864 : checkChunk context facts instructions 20864 128 = true := by decide +kernel

theorem checked_20992 : checkChunk context facts instructions 20992 128 = true := by decide +kernel

theorem checked_21120 : checkChunk context facts instructions 21120 128 = true := by decide +kernel

theorem checked_21248 : checkChunk context facts instructions 21248 128 = true := by decide +kernel

theorem checked_21376 : checkChunk context facts instructions 21376 128 = true := by decide +kernel

theorem holds_block_20480 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 20480 → Holds H g ρ (facts n)) :
    ∀ n, n < 21504 → Holds H g ρ (facts n) := by
  have hall_20480 := checkChunk_sound valid facts instructions 20480 128 prior checked_20480
  have hall_20608 := checkChunk_sound valid facts instructions 20608 128 hall_20480 checked_20608
  have hall_20736 := checkChunk_sound valid facts instructions 20736 128 hall_20608 checked_20736
  have hall_20864 := checkChunk_sound valid facts instructions 20864 128 hall_20736 checked_20864
  have hall_20992 := checkChunk_sound valid facts instructions 20992 128 hall_20864 checked_20992
  have hall_21120 := checkChunk_sound valid facts instructions 21120 128 hall_20992 checked_21120
  have hall_21248 := checkChunk_sound valid facts instructions 21248 128 hall_21120 checked_21248
  have hall_21376 := checkChunk_sound valid facts instructions 21376 128 hall_21248 checked_21376
  exact hall_21376

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
