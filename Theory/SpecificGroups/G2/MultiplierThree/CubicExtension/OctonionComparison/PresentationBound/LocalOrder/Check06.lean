module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_6144 : checkChunk context facts instructions 6144 128 = true := by decide +kernel

theorem checked_6272 : checkChunk context facts instructions 6272 128 = true := by decide +kernel

theorem checked_6400 : checkChunk context facts instructions 6400 128 = true := by decide +kernel

theorem checked_6528 : checkChunk context facts instructions 6528 128 = true := by decide +kernel

theorem checked_6656 : checkChunk context facts instructions 6656 128 = true := by decide +kernel

theorem checked_6784 : checkChunk context facts instructions 6784 128 = true := by decide +kernel

theorem checked_6912 : checkChunk context facts instructions 6912 128 = true := by decide +kernel

theorem checked_7040 : checkChunk context facts instructions 7040 128 = true := by decide +kernel

theorem holds_block_6144 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 6144 → Holds H g ρ (facts n)) :
    ∀ n, n < 7168 → Holds H g ρ (facts n) := by
  have hall_6144 := checkChunk_sound valid facts instructions 6144 128 prior checked_6144
  have hall_6272 := checkChunk_sound valid facts instructions 6272 128 hall_6144 checked_6272
  have hall_6400 := checkChunk_sound valid facts instructions 6400 128 hall_6272 checked_6400
  have hall_6528 := checkChunk_sound valid facts instructions 6528 128 hall_6400 checked_6528
  have hall_6656 := checkChunk_sound valid facts instructions 6656 128 hall_6528 checked_6656
  have hall_6784 := checkChunk_sound valid facts instructions 6784 128 hall_6656 checked_6784
  have hall_6912 := checkChunk_sound valid facts instructions 6912 128 hall_6784 checked_6912
  have hall_7040 := checkChunk_sound valid facts instructions 7040 128 hall_6912 checked_7040
  exact hall_7040

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
