module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_71680 : checkChunk context facts instructions 71680 128 = true := by decide +kernel

theorem checked_71808 : checkChunk context facts instructions 71808 128 = true := by decide +kernel

theorem checked_71936 : checkChunk context facts instructions 71936 128 = true := by decide +kernel

theorem checked_72064 : checkChunk context facts instructions 72064 128 = true := by decide +kernel

theorem checked_72192 : checkChunk context facts instructions 72192 128 = true := by decide +kernel

theorem checked_72320 : checkChunk context facts instructions 72320 128 = true := by decide +kernel

theorem checked_72448 : checkChunk context facts instructions 72448 128 = true := by decide +kernel

theorem checked_72576 : checkChunk context facts instructions 72576 128 = true := by decide +kernel

theorem holds_block_71680 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 71680 → Holds H g ρ (facts n)) :
    ∀ n, n < 72704 → Holds H g ρ (facts n) := by
  have hall_71680 := checkChunk_sound valid facts instructions 71680 128 prior checked_71680
  have hall_71808 := checkChunk_sound valid facts instructions 71808 128 hall_71680 checked_71808
  have hall_71936 := checkChunk_sound valid facts instructions 71936 128 hall_71808 checked_71936
  have hall_72064 := checkChunk_sound valid facts instructions 72064 128 hall_71936 checked_72064
  have hall_72192 := checkChunk_sound valid facts instructions 72192 128 hall_72064 checked_72192
  have hall_72320 := checkChunk_sound valid facts instructions 72320 128 hall_72192 checked_72320
  have hall_72448 := checkChunk_sound valid facts instructions 72448 128 hall_72320 checked_72448
  have hall_72576 := checkChunk_sound valid facts instructions 72576 128 hall_72448 checked_72576
  exact hall_72576

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
