module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_82944 : checkChunk context facts instructions 82944 128 = true := by decide +kernel

theorem checked_83072 : checkChunk context facts instructions 83072 128 = true := by decide +kernel

theorem checked_83200 : checkChunk context facts instructions 83200 128 = true := by decide +kernel

theorem checked_83328 : checkChunk context facts instructions 83328 128 = true := by decide +kernel

theorem checked_83456 : checkChunk context facts instructions 83456 128 = true := by decide +kernel

theorem checked_83584 : checkChunk context facts instructions 83584 128 = true := by decide +kernel

theorem checked_83712 : checkChunk context facts instructions 83712 128 = true := by decide +kernel

theorem checked_83840 : checkChunk context facts instructions 83840 128 = true := by decide +kernel

theorem holds_block_82944 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 82944 → Holds H g ρ (facts n)) :
    ∀ n, n < 83968 → Holds H g ρ (facts n) := by
  have hall_82944 := checkChunk_sound valid facts instructions 82944 128 prior checked_82944
  have hall_83072 := checkChunk_sound valid facts instructions 83072 128 hall_82944 checked_83072
  have hall_83200 := checkChunk_sound valid facts instructions 83200 128 hall_83072 checked_83200
  have hall_83328 := checkChunk_sound valid facts instructions 83328 128 hall_83200 checked_83328
  have hall_83456 := checkChunk_sound valid facts instructions 83456 128 hall_83328 checked_83456
  have hall_83584 := checkChunk_sound valid facts instructions 83584 128 hall_83456 checked_83584
  have hall_83712 := checkChunk_sound valid facts instructions 83712 128 hall_83584 checked_83712
  have hall_83840 := checkChunk_sound valid facts instructions 83840 128 hall_83712 checked_83840
  exact hall_83840

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
