module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_13312 : checkChunk context facts instructions 13312 128 = true := by decide +kernel

theorem checked_13440 : checkChunk context facts instructions 13440 128 = true := by decide +kernel

theorem checked_13568 : checkChunk context facts instructions 13568 128 = true := by decide +kernel

theorem checked_13696 : checkChunk context facts instructions 13696 128 = true := by decide +kernel

theorem checked_13824 : checkChunk context facts instructions 13824 128 = true := by decide +kernel

theorem checked_13952 : checkChunk context facts instructions 13952 128 = true := by decide +kernel

theorem checked_14080 : checkChunk context facts instructions 14080 128 = true := by decide +kernel

theorem checked_14208 : checkChunk context facts instructions 14208 128 = true := by decide +kernel

theorem holds_block_13312 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 13312 → Holds H g ρ (facts n)) :
    ∀ n, n < 14336 → Holds H g ρ (facts n) := by
  have hall_13312 := checkChunk_sound valid facts instructions 13312 128 prior checked_13312
  have hall_13440 := checkChunk_sound valid facts instructions 13440 128 hall_13312 checked_13440
  have hall_13568 := checkChunk_sound valid facts instructions 13568 128 hall_13440 checked_13568
  have hall_13696 := checkChunk_sound valid facts instructions 13696 128 hall_13568 checked_13696
  have hall_13824 := checkChunk_sound valid facts instructions 13824 128 hall_13696 checked_13824
  have hall_13952 := checkChunk_sound valid facts instructions 13952 128 hall_13824 checked_13952
  have hall_14080 := checkChunk_sound valid facts instructions 14080 128 hall_13952 checked_14080
  have hall_14208 := checkChunk_sound valid facts instructions 14208 128 hall_14080 checked_14208
  exact hall_14208

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
