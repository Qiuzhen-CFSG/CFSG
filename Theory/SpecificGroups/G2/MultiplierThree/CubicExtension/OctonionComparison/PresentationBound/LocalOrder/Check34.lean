module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_34816 : checkChunk context facts instructions 34816 128 = true := by decide +kernel

theorem checked_34944 : checkChunk context facts instructions 34944 128 = true := by decide +kernel

theorem checked_35072 : checkChunk context facts instructions 35072 128 = true := by decide +kernel

theorem checked_35200 : checkChunk context facts instructions 35200 128 = true := by decide +kernel

theorem checked_35328 : checkChunk context facts instructions 35328 128 = true := by decide +kernel

theorem checked_35456 : checkChunk context facts instructions 35456 128 = true := by decide +kernel

theorem checked_35584 : checkChunk context facts instructions 35584 128 = true := by decide +kernel

theorem checked_35712 : checkChunk context facts instructions 35712 128 = true := by decide +kernel

theorem holds_block_34816 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 34816 → Holds H g ρ (facts n)) :
    ∀ n, n < 35840 → Holds H g ρ (facts n) := by
  have hall_34816 := checkChunk_sound valid facts instructions 34816 128 prior checked_34816
  have hall_34944 := checkChunk_sound valid facts instructions 34944 128 hall_34816 checked_34944
  have hall_35072 := checkChunk_sound valid facts instructions 35072 128 hall_34944 checked_35072
  have hall_35200 := checkChunk_sound valid facts instructions 35200 128 hall_35072 checked_35200
  have hall_35328 := checkChunk_sound valid facts instructions 35328 128 hall_35200 checked_35328
  have hall_35456 := checkChunk_sound valid facts instructions 35456 128 hall_35328 checked_35456
  have hall_35584 := checkChunk_sound valid facts instructions 35584 128 hall_35456 checked_35584
  have hall_35712 := checkChunk_sound valid facts instructions 35712 128 hall_35584 checked_35712
  exact hall_35712

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
