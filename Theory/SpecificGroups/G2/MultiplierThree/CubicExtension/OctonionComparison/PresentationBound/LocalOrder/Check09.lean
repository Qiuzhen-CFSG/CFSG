module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_9216 : checkChunk context facts instructions 9216 128 = true := by decide +kernel

theorem checked_9344 : checkChunk context facts instructions 9344 128 = true := by decide +kernel

theorem checked_9472 : checkChunk context facts instructions 9472 128 = true := by decide +kernel

theorem checked_9600 : checkChunk context facts instructions 9600 128 = true := by decide +kernel

theorem checked_9728 : checkChunk context facts instructions 9728 128 = true := by decide +kernel

theorem checked_9856 : checkChunk context facts instructions 9856 128 = true := by decide +kernel

theorem checked_9984 : checkChunk context facts instructions 9984 128 = true := by decide +kernel

theorem checked_10112 : checkChunk context facts instructions 10112 128 = true := by decide +kernel

theorem holds_block_9216 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 9216 → Holds H g ρ (facts n)) :
    ∀ n, n < 10240 → Holds H g ρ (facts n) := by
  have hall_9216 := checkChunk_sound valid facts instructions 9216 128 prior checked_9216
  have hall_9344 := checkChunk_sound valid facts instructions 9344 128 hall_9216 checked_9344
  have hall_9472 := checkChunk_sound valid facts instructions 9472 128 hall_9344 checked_9472
  have hall_9600 := checkChunk_sound valid facts instructions 9600 128 hall_9472 checked_9600
  have hall_9728 := checkChunk_sound valid facts instructions 9728 128 hall_9600 checked_9728
  have hall_9856 := checkChunk_sound valid facts instructions 9856 128 hall_9728 checked_9856
  have hall_9984 := checkChunk_sound valid facts instructions 9984 128 hall_9856 checked_9984
  have hall_10112 := checkChunk_sound valid facts instructions 10112 128 hall_9984 checked_10112
  exact hall_10112

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
