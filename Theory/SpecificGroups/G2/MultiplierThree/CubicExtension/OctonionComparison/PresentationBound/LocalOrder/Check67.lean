module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_68608 : checkChunk context facts instructions 68608 128 = true := by decide +kernel

theorem checked_68736 : checkChunk context facts instructions 68736 128 = true := by decide +kernel

theorem checked_68864 : checkChunk context facts instructions 68864 128 = true := by decide +kernel

theorem checked_68992 : checkChunk context facts instructions 68992 128 = true := by decide +kernel

theorem checked_69120 : checkChunk context facts instructions 69120 128 = true := by decide +kernel

theorem checked_69248 : checkChunk context facts instructions 69248 128 = true := by decide +kernel

theorem checked_69376 : checkChunk context facts instructions 69376 128 = true := by decide +kernel

theorem checked_69504 : checkChunk context facts instructions 69504 128 = true := by decide +kernel

theorem holds_block_68608 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 68608 → Holds H g ρ (facts n)) :
    ∀ n, n < 69632 → Holds H g ρ (facts n) := by
  have hall_68608 := checkChunk_sound valid facts instructions 68608 128 prior checked_68608
  have hall_68736 := checkChunk_sound valid facts instructions 68736 128 hall_68608 checked_68736
  have hall_68864 := checkChunk_sound valid facts instructions 68864 128 hall_68736 checked_68864
  have hall_68992 := checkChunk_sound valid facts instructions 68992 128 hall_68864 checked_68992
  have hall_69120 := checkChunk_sound valid facts instructions 69120 128 hall_68992 checked_69120
  have hall_69248 := checkChunk_sound valid facts instructions 69248 128 hall_69120 checked_69248
  have hall_69376 := checkChunk_sound valid facts instructions 69376 128 hall_69248 checked_69376
  have hall_69504 := checkChunk_sound valid facts instructions 69504 128 hall_69376 checked_69504
  exact hall_69504

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
