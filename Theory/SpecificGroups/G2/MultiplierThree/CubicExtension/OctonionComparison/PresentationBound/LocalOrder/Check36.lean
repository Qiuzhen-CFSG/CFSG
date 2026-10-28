module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_36864 : checkChunk context facts instructions 36864 128 = true := by decide +kernel

theorem checked_36992 : checkChunk context facts instructions 36992 128 = true := by decide +kernel

theorem checked_37120 : checkChunk context facts instructions 37120 128 = true := by decide +kernel

theorem checked_37248 : checkChunk context facts instructions 37248 128 = true := by decide +kernel

theorem checked_37376 : checkChunk context facts instructions 37376 128 = true := by decide +kernel

theorem checked_37504 : checkChunk context facts instructions 37504 128 = true := by decide +kernel

theorem checked_37632 : checkChunk context facts instructions 37632 128 = true := by decide +kernel

theorem checked_37760 : checkChunk context facts instructions 37760 128 = true := by decide +kernel

theorem holds_block_36864 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 36864 → Holds H g ρ (facts n)) :
    ∀ n, n < 37888 → Holds H g ρ (facts n) := by
  have hall_36864 := checkChunk_sound valid facts instructions 36864 128 prior checked_36864
  have hall_36992 := checkChunk_sound valid facts instructions 36992 128 hall_36864 checked_36992
  have hall_37120 := checkChunk_sound valid facts instructions 37120 128 hall_36992 checked_37120
  have hall_37248 := checkChunk_sound valid facts instructions 37248 128 hall_37120 checked_37248
  have hall_37376 := checkChunk_sound valid facts instructions 37376 128 hall_37248 checked_37376
  have hall_37504 := checkChunk_sound valid facts instructions 37504 128 hall_37376 checked_37504
  have hall_37632 := checkChunk_sound valid facts instructions 37632 128 hall_37504 checked_37632
  have hall_37760 := checkChunk_sound valid facts instructions 37760 128 hall_37632 checked_37760
  exact hall_37760

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
