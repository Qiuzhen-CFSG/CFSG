module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_63488 : checkChunk context facts instructions 63488 128 = true := by decide +kernel

theorem checked_63616 : checkChunk context facts instructions 63616 128 = true := by decide +kernel

theorem checked_63744 : checkChunk context facts instructions 63744 128 = true := by decide +kernel

theorem checked_63872 : checkChunk context facts instructions 63872 128 = true := by decide +kernel

theorem checked_64000 : checkChunk context facts instructions 64000 128 = true := by decide +kernel

theorem checked_64128 : checkChunk context facts instructions 64128 128 = true := by decide +kernel

theorem checked_64256 : checkChunk context facts instructions 64256 128 = true := by decide +kernel

theorem checked_64384 : checkChunk context facts instructions 64384 128 = true := by decide +kernel

theorem holds_block_63488 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 63488 → Holds H g ρ (facts n)) :
    ∀ n, n < 64512 → Holds H g ρ (facts n) := by
  have hall_63488 := checkChunk_sound valid facts instructions 63488 128 prior checked_63488
  have hall_63616 := checkChunk_sound valid facts instructions 63616 128 hall_63488 checked_63616
  have hall_63744 := checkChunk_sound valid facts instructions 63744 128 hall_63616 checked_63744
  have hall_63872 := checkChunk_sound valid facts instructions 63872 128 hall_63744 checked_63872
  have hall_64000 := checkChunk_sound valid facts instructions 64000 128 hall_63872 checked_64000
  have hall_64128 := checkChunk_sound valid facts instructions 64128 128 hall_64000 checked_64128
  have hall_64256 := checkChunk_sound valid facts instructions 64256 128 hall_64128 checked_64256
  have hall_64384 := checkChunk_sound valid facts instructions 64384 128 hall_64256 checked_64384
  exact hall_64384

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
