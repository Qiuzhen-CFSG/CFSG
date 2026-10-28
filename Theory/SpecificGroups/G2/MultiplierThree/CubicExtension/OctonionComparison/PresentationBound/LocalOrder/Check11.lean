module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_11264 : checkChunk context facts instructions 11264 128 = true := by decide +kernel

theorem checked_11392 : checkChunk context facts instructions 11392 128 = true := by decide +kernel

theorem checked_11520 : checkChunk context facts instructions 11520 128 = true := by decide +kernel

theorem checked_11648 : checkChunk context facts instructions 11648 128 = true := by decide +kernel

theorem checked_11776 : checkChunk context facts instructions 11776 128 = true := by decide +kernel

theorem checked_11904 : checkChunk context facts instructions 11904 128 = true := by decide +kernel

theorem checked_12032 : checkChunk context facts instructions 12032 128 = true := by decide +kernel

theorem checked_12160 : checkChunk context facts instructions 12160 128 = true := by decide +kernel

theorem holds_block_11264 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 11264 → Holds H g ρ (facts n)) :
    ∀ n, n < 12288 → Holds H g ρ (facts n) := by
  have hall_11264 := checkChunk_sound valid facts instructions 11264 128 prior checked_11264
  have hall_11392 := checkChunk_sound valid facts instructions 11392 128 hall_11264 checked_11392
  have hall_11520 := checkChunk_sound valid facts instructions 11520 128 hall_11392 checked_11520
  have hall_11648 := checkChunk_sound valid facts instructions 11648 128 hall_11520 checked_11648
  have hall_11776 := checkChunk_sound valid facts instructions 11776 128 hall_11648 checked_11776
  have hall_11904 := checkChunk_sound valid facts instructions 11904 128 hall_11776 checked_11904
  have hall_12032 := checkChunk_sound valid facts instructions 12032 128 hall_11904 checked_12032
  have hall_12160 := checkChunk_sound valid facts instructions 12160 128 hall_12032 checked_12160
  exact hall_12160

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
