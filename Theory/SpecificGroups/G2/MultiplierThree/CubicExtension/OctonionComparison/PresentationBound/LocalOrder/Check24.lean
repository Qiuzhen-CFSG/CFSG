module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_24576 : checkChunk context facts instructions 24576 128 = true := by decide +kernel

theorem checked_24704 : checkChunk context facts instructions 24704 128 = true := by decide +kernel

theorem checked_24832 : checkChunk context facts instructions 24832 128 = true := by decide +kernel

theorem checked_24960 : checkChunk context facts instructions 24960 128 = true := by decide +kernel

theorem checked_25088 : checkChunk context facts instructions 25088 128 = true := by decide +kernel

theorem checked_25216 : checkChunk context facts instructions 25216 128 = true := by decide +kernel

theorem checked_25344 : checkChunk context facts instructions 25344 128 = true := by decide +kernel

theorem checked_25472 : checkChunk context facts instructions 25472 128 = true := by decide +kernel

theorem holds_block_24576 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 24576 → Holds H g ρ (facts n)) :
    ∀ n, n < 25600 → Holds H g ρ (facts n) := by
  have hall_24576 := checkChunk_sound valid facts instructions 24576 128 prior checked_24576
  have hall_24704 := checkChunk_sound valid facts instructions 24704 128 hall_24576 checked_24704
  have hall_24832 := checkChunk_sound valid facts instructions 24832 128 hall_24704 checked_24832
  have hall_24960 := checkChunk_sound valid facts instructions 24960 128 hall_24832 checked_24960
  have hall_25088 := checkChunk_sound valid facts instructions 25088 128 hall_24960 checked_25088
  have hall_25216 := checkChunk_sound valid facts instructions 25216 128 hall_25088 checked_25216
  have hall_25344 := checkChunk_sound valid facts instructions 25344 128 hall_25216 checked_25344
  have hall_25472 := checkChunk_sound valid facts instructions 25472 128 hall_25344 checked_25472
  exact hall_25472

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
