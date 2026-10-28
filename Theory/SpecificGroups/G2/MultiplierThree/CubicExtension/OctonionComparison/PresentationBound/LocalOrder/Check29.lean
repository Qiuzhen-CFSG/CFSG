module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_29696 : checkChunk context facts instructions 29696 128 = true := by decide +kernel

theorem checked_29824 : checkChunk context facts instructions 29824 128 = true := by decide +kernel

theorem checked_29952 : checkChunk context facts instructions 29952 128 = true := by decide +kernel

theorem checked_30080 : checkChunk context facts instructions 30080 128 = true := by decide +kernel

theorem checked_30208 : checkChunk context facts instructions 30208 128 = true := by decide +kernel

theorem checked_30336 : checkChunk context facts instructions 30336 128 = true := by decide +kernel

theorem checked_30464 : checkChunk context facts instructions 30464 128 = true := by decide +kernel

theorem checked_30592 : checkChunk context facts instructions 30592 128 = true := by decide +kernel

theorem holds_block_29696 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 29696 → Holds H g ρ (facts n)) :
    ∀ n, n < 30720 → Holds H g ρ (facts n) := by
  have hall_29696 := checkChunk_sound valid facts instructions 29696 128 prior checked_29696
  have hall_29824 := checkChunk_sound valid facts instructions 29824 128 hall_29696 checked_29824
  have hall_29952 := checkChunk_sound valid facts instructions 29952 128 hall_29824 checked_29952
  have hall_30080 := checkChunk_sound valid facts instructions 30080 128 hall_29952 checked_30080
  have hall_30208 := checkChunk_sound valid facts instructions 30208 128 hall_30080 checked_30208
  have hall_30336 := checkChunk_sound valid facts instructions 30336 128 hall_30208 checked_30336
  have hall_30464 := checkChunk_sound valid facts instructions 30464 128 hall_30336 checked_30464
  have hall_30592 := checkChunk_sound valid facts instructions 30592 128 hall_30464 checked_30592
  exact hall_30592

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
