module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_56320 : checkChunk context facts instructions 56320 128 = true := by decide +kernel

theorem checked_56448 : checkChunk context facts instructions 56448 128 = true := by decide +kernel

theorem checked_56576 : checkChunk context facts instructions 56576 128 = true := by decide +kernel

theorem checked_56704 : checkChunk context facts instructions 56704 128 = true := by decide +kernel

theorem checked_56832 : checkChunk context facts instructions 56832 128 = true := by decide +kernel

theorem checked_56960 : checkChunk context facts instructions 56960 128 = true := by decide +kernel

theorem checked_57088 : checkChunk context facts instructions 57088 128 = true := by decide +kernel

theorem checked_57216 : checkChunk context facts instructions 57216 128 = true := by decide +kernel

theorem holds_block_56320 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 56320 → Holds H g ρ (facts n)) :
    ∀ n, n < 57344 → Holds H g ρ (facts n) := by
  have hall_56320 := checkChunk_sound valid facts instructions 56320 128 prior checked_56320
  have hall_56448 := checkChunk_sound valid facts instructions 56448 128 hall_56320 checked_56448
  have hall_56576 := checkChunk_sound valid facts instructions 56576 128 hall_56448 checked_56576
  have hall_56704 := checkChunk_sound valid facts instructions 56704 128 hall_56576 checked_56704
  have hall_56832 := checkChunk_sound valid facts instructions 56832 128 hall_56704 checked_56832
  have hall_56960 := checkChunk_sound valid facts instructions 56960 128 hall_56832 checked_56960
  have hall_57088 := checkChunk_sound valid facts instructions 57088 128 hall_56960 checked_57088
  have hall_57216 := checkChunk_sound valid facts instructions 57216 128 hall_57088 checked_57216
  exact hall_57216

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
