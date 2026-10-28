module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_77824 : checkChunk context facts instructions 77824 128 = true := by decide +kernel

theorem checked_77952 : checkChunk context facts instructions 77952 128 = true := by decide +kernel

theorem checked_78080 : checkChunk context facts instructions 78080 128 = true := by decide +kernel

theorem checked_78208 : checkChunk context facts instructions 78208 128 = true := by decide +kernel

theorem checked_78336 : checkChunk context facts instructions 78336 128 = true := by decide +kernel

theorem checked_78464 : checkChunk context facts instructions 78464 128 = true := by decide +kernel

theorem checked_78592 : checkChunk context facts instructions 78592 128 = true := by decide +kernel

theorem checked_78720 : checkChunk context facts instructions 78720 128 = true := by decide +kernel

theorem holds_block_77824 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 77824 → Holds H g ρ (facts n)) :
    ∀ n, n < 78848 → Holds H g ρ (facts n) := by
  have hall_77824 := checkChunk_sound valid facts instructions 77824 128 prior checked_77824
  have hall_77952 := checkChunk_sound valid facts instructions 77952 128 hall_77824 checked_77952
  have hall_78080 := checkChunk_sound valid facts instructions 78080 128 hall_77952 checked_78080
  have hall_78208 := checkChunk_sound valid facts instructions 78208 128 hall_78080 checked_78208
  have hall_78336 := checkChunk_sound valid facts instructions 78336 128 hall_78208 checked_78336
  have hall_78464 := checkChunk_sound valid facts instructions 78464 128 hall_78336 checked_78464
  have hall_78592 := checkChunk_sound valid facts instructions 78592 128 hall_78464 checked_78592
  have hall_78720 := checkChunk_sound valid facts instructions 78720 128 hall_78592 checked_78720
  exact hall_78720

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
