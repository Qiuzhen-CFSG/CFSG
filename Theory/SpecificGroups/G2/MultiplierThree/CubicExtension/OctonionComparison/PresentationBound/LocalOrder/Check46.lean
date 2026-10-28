module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_47104 : checkChunk context facts instructions 47104 128 = true := by decide +kernel

theorem checked_47232 : checkChunk context facts instructions 47232 128 = true := by decide +kernel

theorem checked_47360 : checkChunk context facts instructions 47360 128 = true := by decide +kernel

theorem checked_47488 : checkChunk context facts instructions 47488 128 = true := by decide +kernel

theorem checked_47616 : checkChunk context facts instructions 47616 128 = true := by decide +kernel

theorem checked_47744 : checkChunk context facts instructions 47744 128 = true := by decide +kernel

theorem checked_47872 : checkChunk context facts instructions 47872 128 = true := by decide +kernel

theorem checked_48000 : checkChunk context facts instructions 48000 128 = true := by decide +kernel

theorem holds_block_47104 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 47104 → Holds H g ρ (facts n)) :
    ∀ n, n < 48128 → Holds H g ρ (facts n) := by
  have hall_47104 := checkChunk_sound valid facts instructions 47104 128 prior checked_47104
  have hall_47232 := checkChunk_sound valid facts instructions 47232 128 hall_47104 checked_47232
  have hall_47360 := checkChunk_sound valid facts instructions 47360 128 hall_47232 checked_47360
  have hall_47488 := checkChunk_sound valid facts instructions 47488 128 hall_47360 checked_47488
  have hall_47616 := checkChunk_sound valid facts instructions 47616 128 hall_47488 checked_47616
  have hall_47744 := checkChunk_sound valid facts instructions 47744 128 hall_47616 checked_47744
  have hall_47872 := checkChunk_sound valid facts instructions 47872 128 hall_47744 checked_47872
  have hall_48000 := checkChunk_sound valid facts instructions 48000 128 hall_47872 checked_48000
  exact hall_48000

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
