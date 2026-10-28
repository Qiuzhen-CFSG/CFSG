module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_75776 : checkChunk context facts instructions 75776 128 = true := by decide +kernel

theorem checked_75904 : checkChunk context facts instructions 75904 128 = true := by decide +kernel

theorem checked_76032 : checkChunk context facts instructions 76032 128 = true := by decide +kernel

theorem checked_76160 : checkChunk context facts instructions 76160 128 = true := by decide +kernel

theorem checked_76288 : checkChunk context facts instructions 76288 128 = true := by decide +kernel

theorem checked_76416 : checkChunk context facts instructions 76416 128 = true := by decide +kernel

theorem checked_76544 : checkChunk context facts instructions 76544 128 = true := by decide +kernel

theorem checked_76672 : checkChunk context facts instructions 76672 128 = true := by decide +kernel

theorem holds_block_75776 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 75776 → Holds H g ρ (facts n)) :
    ∀ n, n < 76800 → Holds H g ρ (facts n) := by
  have hall_75776 := checkChunk_sound valid facts instructions 75776 128 prior checked_75776
  have hall_75904 := checkChunk_sound valid facts instructions 75904 128 hall_75776 checked_75904
  have hall_76032 := checkChunk_sound valid facts instructions 76032 128 hall_75904 checked_76032
  have hall_76160 := checkChunk_sound valid facts instructions 76160 128 hall_76032 checked_76160
  have hall_76288 := checkChunk_sound valid facts instructions 76288 128 hall_76160 checked_76288
  have hall_76416 := checkChunk_sound valid facts instructions 76416 128 hall_76288 checked_76416
  have hall_76544 := checkChunk_sound valid facts instructions 76544 128 hall_76416 checked_76544
  have hall_76672 := checkChunk_sound valid facts instructions 76672 128 hall_76544 checked_76672
  exact hall_76672

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
