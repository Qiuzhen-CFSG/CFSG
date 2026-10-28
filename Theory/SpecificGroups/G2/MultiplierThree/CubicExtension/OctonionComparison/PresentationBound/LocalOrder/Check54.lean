module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_55296 : checkChunk context facts instructions 55296 128 = true := by decide +kernel

theorem checked_55424 : checkChunk context facts instructions 55424 128 = true := by decide +kernel

theorem checked_55552 : checkChunk context facts instructions 55552 128 = true := by decide +kernel

theorem checked_55680 : checkChunk context facts instructions 55680 128 = true := by decide +kernel

theorem checked_55808 : checkChunk context facts instructions 55808 128 = true := by decide +kernel

theorem checked_55936 : checkChunk context facts instructions 55936 128 = true := by decide +kernel

theorem checked_56064 : checkChunk context facts instructions 56064 128 = true := by decide +kernel

theorem checked_56192 : checkChunk context facts instructions 56192 128 = true := by decide +kernel

theorem holds_block_55296 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 55296 → Holds H g ρ (facts n)) :
    ∀ n, n < 56320 → Holds H g ρ (facts n) := by
  have hall_55296 := checkChunk_sound valid facts instructions 55296 128 prior checked_55296
  have hall_55424 := checkChunk_sound valid facts instructions 55424 128 hall_55296 checked_55424
  have hall_55552 := checkChunk_sound valid facts instructions 55552 128 hall_55424 checked_55552
  have hall_55680 := checkChunk_sound valid facts instructions 55680 128 hall_55552 checked_55680
  have hall_55808 := checkChunk_sound valid facts instructions 55808 128 hall_55680 checked_55808
  have hall_55936 := checkChunk_sound valid facts instructions 55936 128 hall_55808 checked_55936
  have hall_56064 := checkChunk_sound valid facts instructions 56064 128 hall_55936 checked_56064
  have hall_56192 := checkChunk_sound valid facts instructions 56192 128 hall_56064 checked_56192
  exact hall_56192

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
