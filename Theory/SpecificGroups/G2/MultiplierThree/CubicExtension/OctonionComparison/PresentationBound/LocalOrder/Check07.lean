module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_7168 : checkChunk context facts instructions 7168 128 = true := by decide +kernel

theorem checked_7296 : checkChunk context facts instructions 7296 128 = true := by decide +kernel

theorem checked_7424 : checkChunk context facts instructions 7424 128 = true := by decide +kernel

theorem checked_7552 : checkChunk context facts instructions 7552 128 = true := by decide +kernel

theorem checked_7680 : checkChunk context facts instructions 7680 128 = true := by decide +kernel

theorem checked_7808 : checkChunk context facts instructions 7808 128 = true := by decide +kernel

theorem checked_7936 : checkChunk context facts instructions 7936 128 = true := by decide +kernel

theorem checked_8064 : checkChunk context facts instructions 8064 128 = true := by decide +kernel

theorem holds_block_7168 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 7168 → Holds H g ρ (facts n)) :
    ∀ n, n < 8192 → Holds H g ρ (facts n) := by
  have hall_7168 := checkChunk_sound valid facts instructions 7168 128 prior checked_7168
  have hall_7296 := checkChunk_sound valid facts instructions 7296 128 hall_7168 checked_7296
  have hall_7424 := checkChunk_sound valid facts instructions 7424 128 hall_7296 checked_7424
  have hall_7552 := checkChunk_sound valid facts instructions 7552 128 hall_7424 checked_7552
  have hall_7680 := checkChunk_sound valid facts instructions 7680 128 hall_7552 checked_7680
  have hall_7808 := checkChunk_sound valid facts instructions 7808 128 hall_7680 checked_7808
  have hall_7936 := checkChunk_sound valid facts instructions 7936 128 hall_7808 checked_7936
  have hall_8064 := checkChunk_sound valid facts instructions 8064 128 hall_7936 checked_8064
  exact hall_8064

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
