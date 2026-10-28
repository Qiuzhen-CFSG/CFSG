module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_45056 : checkChunk context facts instructions 45056 128 = true := by decide +kernel

theorem checked_45184 : checkChunk context facts instructions 45184 128 = true := by decide +kernel

theorem checked_45312 : checkChunk context facts instructions 45312 128 = true := by decide +kernel

theorem checked_45440 : checkChunk context facts instructions 45440 128 = true := by decide +kernel

theorem checked_45568 : checkChunk context facts instructions 45568 128 = true := by decide +kernel

theorem checked_45696 : checkChunk context facts instructions 45696 128 = true := by decide +kernel

theorem checked_45824 : checkChunk context facts instructions 45824 128 = true := by decide +kernel

theorem checked_45952 : checkChunk context facts instructions 45952 128 = true := by decide +kernel

theorem holds_block_45056 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 45056 → Holds H g ρ (facts n)) :
    ∀ n, n < 46080 → Holds H g ρ (facts n) := by
  have hall_45056 := checkChunk_sound valid facts instructions 45056 128 prior checked_45056
  have hall_45184 := checkChunk_sound valid facts instructions 45184 128 hall_45056 checked_45184
  have hall_45312 := checkChunk_sound valid facts instructions 45312 128 hall_45184 checked_45312
  have hall_45440 := checkChunk_sound valid facts instructions 45440 128 hall_45312 checked_45440
  have hall_45568 := checkChunk_sound valid facts instructions 45568 128 hall_45440 checked_45568
  have hall_45696 := checkChunk_sound valid facts instructions 45696 128 hall_45568 checked_45696
  have hall_45824 := checkChunk_sound valid facts instructions 45824 128 hall_45696 checked_45824
  have hall_45952 := checkChunk_sound valid facts instructions 45952 128 hall_45824 checked_45952
  exact hall_45952

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
