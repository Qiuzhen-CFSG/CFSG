module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_3072 : checkChunk context facts instructions 3072 128 = true := by decide +kernel

theorem checked_3200 : checkChunk context facts instructions 3200 128 = true := by decide +kernel

theorem checked_3328 : checkChunk context facts instructions 3328 128 = true := by decide +kernel

theorem checked_3456 : checkChunk context facts instructions 3456 128 = true := by decide +kernel

theorem checked_3584 : checkChunk context facts instructions 3584 128 = true := by decide +kernel

theorem checked_3712 : checkChunk context facts instructions 3712 128 = true := by decide +kernel

theorem checked_3840 : checkChunk context facts instructions 3840 128 = true := by decide +kernel

theorem checked_3968 : checkChunk context facts instructions 3968 128 = true := by decide +kernel

theorem holds_block_3072 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 3072 → Holds H g ρ (facts n)) :
    ∀ n, n < 4096 → Holds H g ρ (facts n) := by
  have hall_3072 := checkChunk_sound valid facts instructions 3072 128 prior checked_3072
  have hall_3200 := checkChunk_sound valid facts instructions 3200 128 hall_3072 checked_3200
  have hall_3328 := checkChunk_sound valid facts instructions 3328 128 hall_3200 checked_3328
  have hall_3456 := checkChunk_sound valid facts instructions 3456 128 hall_3328 checked_3456
  have hall_3584 := checkChunk_sound valid facts instructions 3584 128 hall_3456 checked_3584
  have hall_3712 := checkChunk_sound valid facts instructions 3712 128 hall_3584 checked_3712
  have hall_3840 := checkChunk_sound valid facts instructions 3840 128 hall_3712 checked_3840
  have hall_3968 := checkChunk_sound valid facts instructions 3968 128 hall_3840 checked_3968
  exact hall_3968

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
