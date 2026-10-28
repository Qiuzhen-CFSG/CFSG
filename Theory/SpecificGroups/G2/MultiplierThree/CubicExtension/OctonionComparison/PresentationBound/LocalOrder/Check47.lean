module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_48128 : checkChunk context facts instructions 48128 128 = true := by decide +kernel

theorem checked_48256 : checkChunk context facts instructions 48256 128 = true := by decide +kernel

theorem checked_48384 : checkChunk context facts instructions 48384 128 = true := by decide +kernel

theorem checked_48512 : checkChunk context facts instructions 48512 128 = true := by decide +kernel

theorem checked_48640 : checkChunk context facts instructions 48640 128 = true := by decide +kernel

theorem checked_48768 : checkChunk context facts instructions 48768 128 = true := by decide +kernel

theorem checked_48896 : checkChunk context facts instructions 48896 128 = true := by decide +kernel

theorem checked_49024 : checkChunk context facts instructions 49024 128 = true := by decide +kernel

theorem holds_block_48128 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 48128 → Holds H g ρ (facts n)) :
    ∀ n, n < 49152 → Holds H g ρ (facts n) := by
  have hall_48128 := checkChunk_sound valid facts instructions 48128 128 prior checked_48128
  have hall_48256 := checkChunk_sound valid facts instructions 48256 128 hall_48128 checked_48256
  have hall_48384 := checkChunk_sound valid facts instructions 48384 128 hall_48256 checked_48384
  have hall_48512 := checkChunk_sound valid facts instructions 48512 128 hall_48384 checked_48512
  have hall_48640 := checkChunk_sound valid facts instructions 48640 128 hall_48512 checked_48640
  have hall_48768 := checkChunk_sound valid facts instructions 48768 128 hall_48640 checked_48768
  have hall_48896 := checkChunk_sound valid facts instructions 48896 128 hall_48768 checked_48896
  have hall_49024 := checkChunk_sound valid facts instructions 49024 128 hall_48896 checked_49024
  exact hall_49024

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
