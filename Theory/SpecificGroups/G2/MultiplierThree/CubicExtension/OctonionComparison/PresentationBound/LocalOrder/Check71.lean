module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_72704 : checkChunk context facts instructions 72704 128 = true := by decide +kernel

theorem checked_72832 : checkChunk context facts instructions 72832 128 = true := by decide +kernel

theorem checked_72960 : checkChunk context facts instructions 72960 128 = true := by decide +kernel

theorem checked_73088 : checkChunk context facts instructions 73088 128 = true := by decide +kernel

theorem checked_73216 : checkChunk context facts instructions 73216 128 = true := by decide +kernel

theorem checked_73344 : checkChunk context facts instructions 73344 128 = true := by decide +kernel

theorem checked_73472 : checkChunk context facts instructions 73472 128 = true := by decide +kernel

theorem checked_73600 : checkChunk context facts instructions 73600 128 = true := by decide +kernel

theorem holds_block_72704 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 72704 → Holds H g ρ (facts n)) :
    ∀ n, n < 73728 → Holds H g ρ (facts n) := by
  have hall_72704 := checkChunk_sound valid facts instructions 72704 128 prior checked_72704
  have hall_72832 := checkChunk_sound valid facts instructions 72832 128 hall_72704 checked_72832
  have hall_72960 := checkChunk_sound valid facts instructions 72960 128 hall_72832 checked_72960
  have hall_73088 := checkChunk_sound valid facts instructions 73088 128 hall_72960 checked_73088
  have hall_73216 := checkChunk_sound valid facts instructions 73216 128 hall_73088 checked_73216
  have hall_73344 := checkChunk_sound valid facts instructions 73344 128 hall_73216 checked_73344
  have hall_73472 := checkChunk_sound valid facts instructions 73472 128 hall_73344 checked_73472
  have hall_73600 := checkChunk_sound valid facts instructions 73600 128 hall_73472 checked_73600
  exact hall_73600

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
