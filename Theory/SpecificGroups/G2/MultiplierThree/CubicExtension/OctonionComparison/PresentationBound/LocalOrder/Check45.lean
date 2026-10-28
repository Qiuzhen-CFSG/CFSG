module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_46080 : checkChunk context facts instructions 46080 128 = true := by decide +kernel

theorem checked_46208 : checkChunk context facts instructions 46208 128 = true := by decide +kernel

theorem checked_46336 : checkChunk context facts instructions 46336 128 = true := by decide +kernel

theorem checked_46464 : checkChunk context facts instructions 46464 128 = true := by decide +kernel

theorem checked_46592 : checkChunk context facts instructions 46592 128 = true := by decide +kernel

theorem checked_46720 : checkChunk context facts instructions 46720 128 = true := by decide +kernel

theorem checked_46848 : checkChunk context facts instructions 46848 128 = true := by decide +kernel

theorem checked_46976 : checkChunk context facts instructions 46976 128 = true := by decide +kernel

theorem holds_block_46080 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 46080 → Holds H g ρ (facts n)) :
    ∀ n, n < 47104 → Holds H g ρ (facts n) := by
  have hall_46080 := checkChunk_sound valid facts instructions 46080 128 prior checked_46080
  have hall_46208 := checkChunk_sound valid facts instructions 46208 128 hall_46080 checked_46208
  have hall_46336 := checkChunk_sound valid facts instructions 46336 128 hall_46208 checked_46336
  have hall_46464 := checkChunk_sound valid facts instructions 46464 128 hall_46336 checked_46464
  have hall_46592 := checkChunk_sound valid facts instructions 46592 128 hall_46464 checked_46592
  have hall_46720 := checkChunk_sound valid facts instructions 46720 128 hall_46592 checked_46720
  have hall_46848 := checkChunk_sound valid facts instructions 46848 128 hall_46720 checked_46848
  have hall_46976 := checkChunk_sound valid facts instructions 46976 128 hall_46848 checked_46976
  exact hall_46976

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
