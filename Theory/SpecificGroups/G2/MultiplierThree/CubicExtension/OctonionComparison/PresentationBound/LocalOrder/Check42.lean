module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_43008 : checkChunk context facts instructions 43008 128 = true := by decide +kernel

theorem checked_43136 : checkChunk context facts instructions 43136 128 = true := by decide +kernel

theorem checked_43264 : checkChunk context facts instructions 43264 128 = true := by decide +kernel

theorem checked_43392 : checkChunk context facts instructions 43392 128 = true := by decide +kernel

theorem checked_43520 : checkChunk context facts instructions 43520 128 = true := by decide +kernel

theorem checked_43648 : checkChunk context facts instructions 43648 128 = true := by decide +kernel

theorem checked_43776 : checkChunk context facts instructions 43776 128 = true := by decide +kernel

theorem checked_43904 : checkChunk context facts instructions 43904 128 = true := by decide +kernel

theorem holds_block_43008 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 43008 → Holds H g ρ (facts n)) :
    ∀ n, n < 44032 → Holds H g ρ (facts n) := by
  have hall_43008 := checkChunk_sound valid facts instructions 43008 128 prior checked_43008
  have hall_43136 := checkChunk_sound valid facts instructions 43136 128 hall_43008 checked_43136
  have hall_43264 := checkChunk_sound valid facts instructions 43264 128 hall_43136 checked_43264
  have hall_43392 := checkChunk_sound valid facts instructions 43392 128 hall_43264 checked_43392
  have hall_43520 := checkChunk_sound valid facts instructions 43520 128 hall_43392 checked_43520
  have hall_43648 := checkChunk_sound valid facts instructions 43648 128 hall_43520 checked_43648
  have hall_43776 := checkChunk_sound valid facts instructions 43776 128 hall_43648 checked_43776
  have hall_43904 := checkChunk_sound valid facts instructions 43904 128 hall_43776 checked_43904
  exact hall_43904

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
