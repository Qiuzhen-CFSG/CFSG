module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_80896 : checkChunk context facts instructions 80896 128 = true := by decide +kernel

theorem checked_81024 : checkChunk context facts instructions 81024 128 = true := by decide +kernel

theorem checked_81152 : checkChunk context facts instructions 81152 128 = true := by decide +kernel

theorem checked_81280 : checkChunk context facts instructions 81280 128 = true := by decide +kernel

theorem checked_81408 : checkChunk context facts instructions 81408 128 = true := by decide +kernel

theorem checked_81536 : checkChunk context facts instructions 81536 128 = true := by decide +kernel

theorem checked_81664 : checkChunk context facts instructions 81664 128 = true := by decide +kernel

theorem checked_81792 : checkChunk context facts instructions 81792 128 = true := by decide +kernel

theorem holds_block_80896 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 80896 → Holds H g ρ (facts n)) :
    ∀ n, n < 81920 → Holds H g ρ (facts n) := by
  have hall_80896 := checkChunk_sound valid facts instructions 80896 128 prior checked_80896
  have hall_81024 := checkChunk_sound valid facts instructions 81024 128 hall_80896 checked_81024
  have hall_81152 := checkChunk_sound valid facts instructions 81152 128 hall_81024 checked_81152
  have hall_81280 := checkChunk_sound valid facts instructions 81280 128 hall_81152 checked_81280
  have hall_81408 := checkChunk_sound valid facts instructions 81408 128 hall_81280 checked_81408
  have hall_81536 := checkChunk_sound valid facts instructions 81536 128 hall_81408 checked_81536
  have hall_81664 := checkChunk_sound valid facts instructions 81664 128 hall_81536 checked_81664
  have hall_81792 := checkChunk_sound valid facts instructions 81792 128 hall_81664 checked_81792
  exact hall_81792

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
