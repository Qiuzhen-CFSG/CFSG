module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_79872 : checkChunk context facts instructions 79872 128 = true := by decide +kernel

theorem checked_80000 : checkChunk context facts instructions 80000 128 = true := by decide +kernel

theorem checked_80128 : checkChunk context facts instructions 80128 128 = true := by decide +kernel

theorem checked_80256 : checkChunk context facts instructions 80256 128 = true := by decide +kernel

theorem checked_80384 : checkChunk context facts instructions 80384 128 = true := by decide +kernel

theorem checked_80512 : checkChunk context facts instructions 80512 128 = true := by decide +kernel

theorem checked_80640 : checkChunk context facts instructions 80640 128 = true := by decide +kernel

theorem checked_80768 : checkChunk context facts instructions 80768 128 = true := by decide +kernel

theorem holds_block_79872 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 79872 → Holds H g ρ (facts n)) :
    ∀ n, n < 80896 → Holds H g ρ (facts n) := by
  have hall_79872 := checkChunk_sound valid facts instructions 79872 128 prior checked_79872
  have hall_80000 := checkChunk_sound valid facts instructions 80000 128 hall_79872 checked_80000
  have hall_80128 := checkChunk_sound valid facts instructions 80128 128 hall_80000 checked_80128
  have hall_80256 := checkChunk_sound valid facts instructions 80256 128 hall_80128 checked_80256
  have hall_80384 := checkChunk_sound valid facts instructions 80384 128 hall_80256 checked_80384
  have hall_80512 := checkChunk_sound valid facts instructions 80512 128 hall_80384 checked_80512
  have hall_80640 := checkChunk_sound valid facts instructions 80640 128 hall_80512 checked_80640
  have hall_80768 := checkChunk_sound valid facts instructions 80768 128 hall_80640 checked_80768
  exact hall_80768

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
