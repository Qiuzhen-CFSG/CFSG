module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_4096 : checkChunk context facts instructions 4096 128 = true := by decide +kernel

theorem checked_4224 : checkChunk context facts instructions 4224 128 = true := by decide +kernel

theorem checked_4352 : checkChunk context facts instructions 4352 128 = true := by decide +kernel

theorem checked_4480 : checkChunk context facts instructions 4480 128 = true := by decide +kernel

theorem checked_4608 : checkChunk context facts instructions 4608 128 = true := by decide +kernel

theorem checked_4736 : checkChunk context facts instructions 4736 128 = true := by decide +kernel

theorem checked_4864 : checkChunk context facts instructions 4864 128 = true := by decide +kernel

theorem checked_4992 : checkChunk context facts instructions 4992 128 = true := by decide +kernel

theorem holds_block_4096 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 4096 → Holds H g ρ (facts n)) :
    ∀ n, n < 5120 → Holds H g ρ (facts n) := by
  have hall_4096 := checkChunk_sound valid facts instructions 4096 128 prior checked_4096
  have hall_4224 := checkChunk_sound valid facts instructions 4224 128 hall_4096 checked_4224
  have hall_4352 := checkChunk_sound valid facts instructions 4352 128 hall_4224 checked_4352
  have hall_4480 := checkChunk_sound valid facts instructions 4480 128 hall_4352 checked_4480
  have hall_4608 := checkChunk_sound valid facts instructions 4608 128 hall_4480 checked_4608
  have hall_4736 := checkChunk_sound valid facts instructions 4736 128 hall_4608 checked_4736
  have hall_4864 := checkChunk_sound valid facts instructions 4864 128 hall_4736 checked_4864
  have hall_4992 := checkChunk_sound valid facts instructions 4992 128 hall_4864 checked_4992
  exact hall_4992

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
