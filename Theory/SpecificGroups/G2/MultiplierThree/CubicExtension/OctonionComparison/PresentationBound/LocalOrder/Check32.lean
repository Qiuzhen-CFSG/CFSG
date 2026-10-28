module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_32768 : checkChunk context facts instructions 32768 128 = true := by decide +kernel

theorem checked_32896 : checkChunk context facts instructions 32896 128 = true := by decide +kernel

theorem checked_33024 : checkChunk context facts instructions 33024 128 = true := by decide +kernel

theorem checked_33152 : checkChunk context facts instructions 33152 128 = true := by decide +kernel

theorem checked_33280 : checkChunk context facts instructions 33280 128 = true := by decide +kernel

theorem checked_33408 : checkChunk context facts instructions 33408 128 = true := by decide +kernel

theorem checked_33536 : checkChunk context facts instructions 33536 128 = true := by decide +kernel

theorem checked_33664 : checkChunk context facts instructions 33664 128 = true := by decide +kernel

theorem holds_block_32768 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 32768 → Holds H g ρ (facts n)) :
    ∀ n, n < 33792 → Holds H g ρ (facts n) := by
  have hall_32768 := checkChunk_sound valid facts instructions 32768 128 prior checked_32768
  have hall_32896 := checkChunk_sound valid facts instructions 32896 128 hall_32768 checked_32896
  have hall_33024 := checkChunk_sound valid facts instructions 33024 128 hall_32896 checked_33024
  have hall_33152 := checkChunk_sound valid facts instructions 33152 128 hall_33024 checked_33152
  have hall_33280 := checkChunk_sound valid facts instructions 33280 128 hall_33152 checked_33280
  have hall_33408 := checkChunk_sound valid facts instructions 33408 128 hall_33280 checked_33408
  have hall_33536 := checkChunk_sound valid facts instructions 33536 128 hall_33408 checked_33536
  have hall_33664 := checkChunk_sound valid facts instructions 33664 128 hall_33536 checked_33664
  exact hall_33664

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
