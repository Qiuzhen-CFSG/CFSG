module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_35840 : checkChunk context facts instructions 35840 128 = true := by decide +kernel

theorem checked_35968 : checkChunk context facts instructions 35968 128 = true := by decide +kernel

theorem checked_36096 : checkChunk context facts instructions 36096 128 = true := by decide +kernel

theorem checked_36224 : checkChunk context facts instructions 36224 128 = true := by decide +kernel

theorem checked_36352 : checkChunk context facts instructions 36352 128 = true := by decide +kernel

theorem checked_36480 : checkChunk context facts instructions 36480 128 = true := by decide +kernel

theorem checked_36608 : checkChunk context facts instructions 36608 128 = true := by decide +kernel

theorem checked_36736 : checkChunk context facts instructions 36736 128 = true := by decide +kernel

theorem holds_block_35840 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 35840 → Holds H g ρ (facts n)) :
    ∀ n, n < 36864 → Holds H g ρ (facts n) := by
  have hall_35840 := checkChunk_sound valid facts instructions 35840 128 prior checked_35840
  have hall_35968 := checkChunk_sound valid facts instructions 35968 128 hall_35840 checked_35968
  have hall_36096 := checkChunk_sound valid facts instructions 36096 128 hall_35968 checked_36096
  have hall_36224 := checkChunk_sound valid facts instructions 36224 128 hall_36096 checked_36224
  have hall_36352 := checkChunk_sound valid facts instructions 36352 128 hall_36224 checked_36352
  have hall_36480 := checkChunk_sound valid facts instructions 36480 128 hall_36352 checked_36480
  have hall_36608 := checkChunk_sound valid facts instructions 36608 128 hall_36480 checked_36608
  have hall_36736 := checkChunk_sound valid facts instructions 36736 128 hall_36608 checked_36736
  exact hall_36736

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
