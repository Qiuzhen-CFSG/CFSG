module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_40960 : checkChunk context facts instructions 40960 128 = true := by decide +kernel

theorem checked_41088 : checkChunk context facts instructions 41088 128 = true := by decide +kernel

theorem checked_41216 : checkChunk context facts instructions 41216 128 = true := by decide +kernel

theorem checked_41344 : checkChunk context facts instructions 41344 128 = true := by decide +kernel

theorem checked_41472 : checkChunk context facts instructions 41472 128 = true := by decide +kernel

theorem checked_41600 : checkChunk context facts instructions 41600 128 = true := by decide +kernel

theorem checked_41728 : checkChunk context facts instructions 41728 128 = true := by decide +kernel

theorem checked_41856 : checkChunk context facts instructions 41856 128 = true := by decide +kernel

theorem holds_block_40960 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 40960 → Holds H g ρ (facts n)) :
    ∀ n, n < 41984 → Holds H g ρ (facts n) := by
  have hall_40960 := checkChunk_sound valid facts instructions 40960 128 prior checked_40960
  have hall_41088 := checkChunk_sound valid facts instructions 41088 128 hall_40960 checked_41088
  have hall_41216 := checkChunk_sound valid facts instructions 41216 128 hall_41088 checked_41216
  have hall_41344 := checkChunk_sound valid facts instructions 41344 128 hall_41216 checked_41344
  have hall_41472 := checkChunk_sound valid facts instructions 41472 128 hall_41344 checked_41472
  have hall_41600 := checkChunk_sound valid facts instructions 41600 128 hall_41472 checked_41600
  have hall_41728 := checkChunk_sound valid facts instructions 41728 128 hall_41600 checked_41728
  have hall_41856 := checkChunk_sound valid facts instructions 41856 128 hall_41728 checked_41856
  exact hall_41856

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
