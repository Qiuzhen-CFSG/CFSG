module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_21504 : checkChunk context facts instructions 21504 128 = true := by decide +kernel

theorem checked_21632 : checkChunk context facts instructions 21632 128 = true := by decide +kernel

theorem checked_21760 : checkChunk context facts instructions 21760 128 = true := by decide +kernel

theorem checked_21888 : checkChunk context facts instructions 21888 128 = true := by decide +kernel

theorem checked_22016 : checkChunk context facts instructions 22016 128 = true := by decide +kernel

theorem checked_22144 : checkChunk context facts instructions 22144 128 = true := by decide +kernel

theorem checked_22272 : checkChunk context facts instructions 22272 128 = true := by decide +kernel

theorem checked_22400 : checkChunk context facts instructions 22400 128 = true := by decide +kernel

theorem holds_block_21504 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 21504 → Holds H g ρ (facts n)) :
    ∀ n, n < 22528 → Holds H g ρ (facts n) := by
  have hall_21504 := checkChunk_sound valid facts instructions 21504 128 prior checked_21504
  have hall_21632 := checkChunk_sound valid facts instructions 21632 128 hall_21504 checked_21632
  have hall_21760 := checkChunk_sound valid facts instructions 21760 128 hall_21632 checked_21760
  have hall_21888 := checkChunk_sound valid facts instructions 21888 128 hall_21760 checked_21888
  have hall_22016 := checkChunk_sound valid facts instructions 22016 128 hall_21888 checked_22016
  have hall_22144 := checkChunk_sound valid facts instructions 22144 128 hall_22016 checked_22144
  have hall_22272 := checkChunk_sound valid facts instructions 22272 128 hall_22144 checked_22272
  have hall_22400 := checkChunk_sound valid facts instructions 22400 128 hall_22272 checked_22400
  exact hall_22400

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
