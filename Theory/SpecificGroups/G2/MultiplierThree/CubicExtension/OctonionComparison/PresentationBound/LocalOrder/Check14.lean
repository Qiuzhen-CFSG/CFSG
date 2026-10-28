module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_14336 : checkChunk context facts instructions 14336 128 = true := by decide +kernel

theorem checked_14464 : checkChunk context facts instructions 14464 128 = true := by decide +kernel

theorem checked_14592 : checkChunk context facts instructions 14592 128 = true := by decide +kernel

theorem checked_14720 : checkChunk context facts instructions 14720 128 = true := by decide +kernel

theorem checked_14848 : checkChunk context facts instructions 14848 128 = true := by decide +kernel

theorem checked_14976 : checkChunk context facts instructions 14976 128 = true := by decide +kernel

theorem checked_15104 : checkChunk context facts instructions 15104 128 = true := by decide +kernel

theorem checked_15232 : checkChunk context facts instructions 15232 128 = true := by decide +kernel

theorem holds_block_14336 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 14336 → Holds H g ρ (facts n)) :
    ∀ n, n < 15360 → Holds H g ρ (facts n) := by
  have hall_14336 := checkChunk_sound valid facts instructions 14336 128 prior checked_14336
  have hall_14464 := checkChunk_sound valid facts instructions 14464 128 hall_14336 checked_14464
  have hall_14592 := checkChunk_sound valid facts instructions 14592 128 hall_14464 checked_14592
  have hall_14720 := checkChunk_sound valid facts instructions 14720 128 hall_14592 checked_14720
  have hall_14848 := checkChunk_sound valid facts instructions 14848 128 hall_14720 checked_14848
  have hall_14976 := checkChunk_sound valid facts instructions 14976 128 hall_14848 checked_14976
  have hall_15104 := checkChunk_sound valid facts instructions 15104 128 hall_14976 checked_15104
  have hall_15232 := checkChunk_sound valid facts instructions 15232 128 hall_15104 checked_15232
  exact hall_15232

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
