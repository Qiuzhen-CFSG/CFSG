module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_16384 : checkChunk context facts instructions 16384 128 = true := by decide +kernel

theorem checked_16512 : checkChunk context facts instructions 16512 128 = true := by decide +kernel

theorem checked_16640 : checkChunk context facts instructions 16640 128 = true := by decide +kernel

theorem checked_16768 : checkChunk context facts instructions 16768 128 = true := by decide +kernel

theorem checked_16896 : checkChunk context facts instructions 16896 128 = true := by decide +kernel

theorem checked_17024 : checkChunk context facts instructions 17024 128 = true := by decide +kernel

theorem checked_17152 : checkChunk context facts instructions 17152 128 = true := by decide +kernel

theorem checked_17280 : checkChunk context facts instructions 17280 128 = true := by decide +kernel

theorem holds_block_16384 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 16384 → Holds H g ρ (facts n)) :
    ∀ n, n < 17408 → Holds H g ρ (facts n) := by
  have hall_16384 := checkChunk_sound valid facts instructions 16384 128 prior checked_16384
  have hall_16512 := checkChunk_sound valid facts instructions 16512 128 hall_16384 checked_16512
  have hall_16640 := checkChunk_sound valid facts instructions 16640 128 hall_16512 checked_16640
  have hall_16768 := checkChunk_sound valid facts instructions 16768 128 hall_16640 checked_16768
  have hall_16896 := checkChunk_sound valid facts instructions 16896 128 hall_16768 checked_16896
  have hall_17024 := checkChunk_sound valid facts instructions 17024 128 hall_16896 checked_17024
  have hall_17152 := checkChunk_sound valid facts instructions 17152 128 hall_17024 checked_17152
  have hall_17280 := checkChunk_sound valid facts instructions 17280 128 hall_17152 checked_17280
  exact hall_17280

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
