module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_27648 : checkChunk context facts instructions 27648 128 = true := by decide +kernel

theorem checked_27776 : checkChunk context facts instructions 27776 128 = true := by decide +kernel

theorem checked_27904 : checkChunk context facts instructions 27904 128 = true := by decide +kernel

theorem checked_28032 : checkChunk context facts instructions 28032 128 = true := by decide +kernel

theorem checked_28160 : checkChunk context facts instructions 28160 128 = true := by decide +kernel

theorem checked_28288 : checkChunk context facts instructions 28288 128 = true := by decide +kernel

theorem checked_28416 : checkChunk context facts instructions 28416 128 = true := by decide +kernel

theorem checked_28544 : checkChunk context facts instructions 28544 128 = true := by decide +kernel

theorem holds_block_27648 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 27648 → Holds H g ρ (facts n)) :
    ∀ n, n < 28672 → Holds H g ρ (facts n) := by
  have hall_27648 := checkChunk_sound valid facts instructions 27648 128 prior checked_27648
  have hall_27776 := checkChunk_sound valid facts instructions 27776 128 hall_27648 checked_27776
  have hall_27904 := checkChunk_sound valid facts instructions 27904 128 hall_27776 checked_27904
  have hall_28032 := checkChunk_sound valid facts instructions 28032 128 hall_27904 checked_28032
  have hall_28160 := checkChunk_sound valid facts instructions 28160 128 hall_28032 checked_28160
  have hall_28288 := checkChunk_sound valid facts instructions 28288 128 hall_28160 checked_28288
  have hall_28416 := checkChunk_sound valid facts instructions 28416 128 hall_28288 checked_28416
  have hall_28544 := checkChunk_sound valid facts instructions 28544 128 hall_28416 checked_28544
  exact hall_28544

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
