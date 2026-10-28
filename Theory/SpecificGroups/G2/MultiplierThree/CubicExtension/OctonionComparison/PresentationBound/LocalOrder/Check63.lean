module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_64512 : checkChunk context facts instructions 64512 128 = true := by decide +kernel

theorem checked_64640 : checkChunk context facts instructions 64640 128 = true := by decide +kernel

theorem checked_64768 : checkChunk context facts instructions 64768 128 = true := by decide +kernel

theorem checked_64896 : checkChunk context facts instructions 64896 128 = true := by decide +kernel

theorem checked_65024 : checkChunk context facts instructions 65024 128 = true := by decide +kernel

theorem checked_65152 : checkChunk context facts instructions 65152 128 = true := by decide +kernel

theorem checked_65280 : checkChunk context facts instructions 65280 128 = true := by decide +kernel

theorem checked_65408 : checkChunk context facts instructions 65408 128 = true := by decide +kernel

theorem holds_block_64512 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 64512 → Holds H g ρ (facts n)) :
    ∀ n, n < 65536 → Holds H g ρ (facts n) := by
  have hall_64512 := checkChunk_sound valid facts instructions 64512 128 prior checked_64512
  have hall_64640 := checkChunk_sound valid facts instructions 64640 128 hall_64512 checked_64640
  have hall_64768 := checkChunk_sound valid facts instructions 64768 128 hall_64640 checked_64768
  have hall_64896 := checkChunk_sound valid facts instructions 64896 128 hall_64768 checked_64896
  have hall_65024 := checkChunk_sound valid facts instructions 65024 128 hall_64896 checked_65024
  have hall_65152 := checkChunk_sound valid facts instructions 65152 128 hall_65024 checked_65152
  have hall_65280 := checkChunk_sound valid facts instructions 65280 128 hall_65152 checked_65280
  have hall_65408 := checkChunk_sound valid facts instructions 65408 128 hall_65280 checked_65408
  exact hall_65408

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
