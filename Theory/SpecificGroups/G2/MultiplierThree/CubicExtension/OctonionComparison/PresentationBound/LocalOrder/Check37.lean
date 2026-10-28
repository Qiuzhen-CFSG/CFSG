module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_37888 : checkChunk context facts instructions 37888 128 = true := by decide +kernel

theorem checked_38016 : checkChunk context facts instructions 38016 128 = true := by decide +kernel

theorem checked_38144 : checkChunk context facts instructions 38144 128 = true := by decide +kernel

theorem checked_38272 : checkChunk context facts instructions 38272 128 = true := by decide +kernel

theorem checked_38400 : checkChunk context facts instructions 38400 128 = true := by decide +kernel

theorem checked_38528 : checkChunk context facts instructions 38528 128 = true := by decide +kernel

theorem checked_38656 : checkChunk context facts instructions 38656 128 = true := by decide +kernel

theorem checked_38784 : checkChunk context facts instructions 38784 128 = true := by decide +kernel

theorem holds_block_37888 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 37888 → Holds H g ρ (facts n)) :
    ∀ n, n < 38912 → Holds H g ρ (facts n) := by
  have hall_37888 := checkChunk_sound valid facts instructions 37888 128 prior checked_37888
  have hall_38016 := checkChunk_sound valid facts instructions 38016 128 hall_37888 checked_38016
  have hall_38144 := checkChunk_sound valid facts instructions 38144 128 hall_38016 checked_38144
  have hall_38272 := checkChunk_sound valid facts instructions 38272 128 hall_38144 checked_38272
  have hall_38400 := checkChunk_sound valid facts instructions 38400 128 hall_38272 checked_38400
  have hall_38528 := checkChunk_sound valid facts instructions 38528 128 hall_38400 checked_38528
  have hall_38656 := checkChunk_sound valid facts instructions 38656 128 hall_38528 checked_38656
  have hall_38784 := checkChunk_sound valid facts instructions 38784 128 hall_38656 checked_38784
  exact hall_38784

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
