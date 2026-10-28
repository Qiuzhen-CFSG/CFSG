module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_83968 : checkChunk context facts instructions 83968 128 = true := by decide +kernel

theorem checked_84096 : checkChunk context facts instructions 84096 128 = true := by decide +kernel

theorem checked_84224 : checkChunk context facts instructions 84224 128 = true := by decide +kernel

theorem checked_84352 : checkChunk context facts instructions 84352 128 = true := by decide +kernel

theorem checked_84480 : checkChunk context facts instructions 84480 128 = true := by decide +kernel

theorem checked_84608 : checkChunk context facts instructions 84608 128 = true := by decide +kernel

theorem checked_84736 : checkChunk context facts instructions 84736 128 = true := by decide +kernel

theorem checked_84864 : checkChunk context facts instructions 84864 128 = true := by decide +kernel

theorem holds_block_83968 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 83968 → Holds H g ρ (facts n)) :
    ∀ n, n < 84992 → Holds H g ρ (facts n) := by
  have hall_83968 := checkChunk_sound valid facts instructions 83968 128 prior checked_83968
  have hall_84096 := checkChunk_sound valid facts instructions 84096 128 hall_83968 checked_84096
  have hall_84224 := checkChunk_sound valid facts instructions 84224 128 hall_84096 checked_84224
  have hall_84352 := checkChunk_sound valid facts instructions 84352 128 hall_84224 checked_84352
  have hall_84480 := checkChunk_sound valid facts instructions 84480 128 hall_84352 checked_84480
  have hall_84608 := checkChunk_sound valid facts instructions 84608 128 hall_84480 checked_84608
  have hall_84736 := checkChunk_sound valid facts instructions 84736 128 hall_84608 checked_84736
  have hall_84864 := checkChunk_sound valid facts instructions 84864 128 hall_84736 checked_84864
  exact hall_84864

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
