module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_10240 : checkChunk context facts instructions 10240 128 = true := by decide +kernel

theorem checked_10368 : checkChunk context facts instructions 10368 128 = true := by decide +kernel

theorem checked_10496 : checkChunk context facts instructions 10496 128 = true := by decide +kernel

theorem checked_10624 : checkChunk context facts instructions 10624 128 = true := by decide +kernel

theorem checked_10752 : checkChunk context facts instructions 10752 128 = true := by decide +kernel

theorem checked_10880 : checkChunk context facts instructions 10880 128 = true := by decide +kernel

theorem checked_11008 : checkChunk context facts instructions 11008 128 = true := by decide +kernel

theorem checked_11136 : checkChunk context facts instructions 11136 128 = true := by decide +kernel

theorem holds_block_10240 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 10240 → Holds H g ρ (facts n)) :
    ∀ n, n < 11264 → Holds H g ρ (facts n) := by
  have hall_10240 := checkChunk_sound valid facts instructions 10240 128 prior checked_10240
  have hall_10368 := checkChunk_sound valid facts instructions 10368 128 hall_10240 checked_10368
  have hall_10496 := checkChunk_sound valid facts instructions 10496 128 hall_10368 checked_10496
  have hall_10624 := checkChunk_sound valid facts instructions 10624 128 hall_10496 checked_10624
  have hall_10752 := checkChunk_sound valid facts instructions 10752 128 hall_10624 checked_10752
  have hall_10880 := checkChunk_sound valid facts instructions 10880 128 hall_10752 checked_10880
  have hall_11008 := checkChunk_sound valid facts instructions 11008 128 hall_10880 checked_11008
  have hall_11136 := checkChunk_sound valid facts instructions 11136 128 hall_11008 checked_11136
  exact hall_11136

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
