module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_76800 : checkChunk context facts instructions 76800 128 = true := by decide +kernel

theorem checked_76928 : checkChunk context facts instructions 76928 128 = true := by decide +kernel

theorem checked_77056 : checkChunk context facts instructions 77056 128 = true := by decide +kernel

theorem checked_77184 : checkChunk context facts instructions 77184 128 = true := by decide +kernel

theorem checked_77312 : checkChunk context facts instructions 77312 128 = true := by decide +kernel

theorem checked_77440 : checkChunk context facts instructions 77440 128 = true := by decide +kernel

theorem checked_77568 : checkChunk context facts instructions 77568 128 = true := by decide +kernel

theorem checked_77696 : checkChunk context facts instructions 77696 128 = true := by decide +kernel

theorem holds_block_76800 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 76800 → Holds H g ρ (facts n)) :
    ∀ n, n < 77824 → Holds H g ρ (facts n) := by
  have hall_76800 := checkChunk_sound valid facts instructions 76800 128 prior checked_76800
  have hall_76928 := checkChunk_sound valid facts instructions 76928 128 hall_76800 checked_76928
  have hall_77056 := checkChunk_sound valid facts instructions 77056 128 hall_76928 checked_77056
  have hall_77184 := checkChunk_sound valid facts instructions 77184 128 hall_77056 checked_77184
  have hall_77312 := checkChunk_sound valid facts instructions 77312 128 hall_77184 checked_77312
  have hall_77440 := checkChunk_sound valid facts instructions 77440 128 hall_77312 checked_77440
  have hall_77568 := checkChunk_sound valid facts instructions 77568 128 hall_77440 checked_77568
  have hall_77696 := checkChunk_sound valid facts instructions 77696 128 hall_77568 checked_77696
  exact hall_77696

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
