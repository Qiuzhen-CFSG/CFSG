module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_28672 : checkChunk context facts instructions 28672 128 = true := by decide +kernel

theorem checked_28800 : checkChunk context facts instructions 28800 128 = true := by decide +kernel

theorem checked_28928 : checkChunk context facts instructions 28928 128 = true := by decide +kernel

theorem checked_29056 : checkChunk context facts instructions 29056 128 = true := by decide +kernel

theorem checked_29184 : checkChunk context facts instructions 29184 128 = true := by decide +kernel

theorem checked_29312 : checkChunk context facts instructions 29312 128 = true := by decide +kernel

theorem checked_29440 : checkChunk context facts instructions 29440 128 = true := by decide +kernel

theorem checked_29568 : checkChunk context facts instructions 29568 128 = true := by decide +kernel

theorem holds_block_28672 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 28672 → Holds H g ρ (facts n)) :
    ∀ n, n < 29696 → Holds H g ρ (facts n) := by
  have hall_28672 := checkChunk_sound valid facts instructions 28672 128 prior checked_28672
  have hall_28800 := checkChunk_sound valid facts instructions 28800 128 hall_28672 checked_28800
  have hall_28928 := checkChunk_sound valid facts instructions 28928 128 hall_28800 checked_28928
  have hall_29056 := checkChunk_sound valid facts instructions 29056 128 hall_28928 checked_29056
  have hall_29184 := checkChunk_sound valid facts instructions 29184 128 hall_29056 checked_29184
  have hall_29312 := checkChunk_sound valid facts instructions 29312 128 hall_29184 checked_29312
  have hall_29440 := checkChunk_sound valid facts instructions 29440 128 hall_29312 checked_29440
  have hall_29568 := checkChunk_sound valid facts instructions 29568 128 hall_29440 checked_29568
  exact hall_29568

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
