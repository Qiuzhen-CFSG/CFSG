module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_8192 : checkChunk context facts instructions 8192 128 = true := by decide +kernel

theorem checked_8320 : checkChunk context facts instructions 8320 128 = true := by decide +kernel

theorem checked_8448 : checkChunk context facts instructions 8448 128 = true := by decide +kernel

theorem checked_8576 : checkChunk context facts instructions 8576 128 = true := by decide +kernel

theorem checked_8704 : checkChunk context facts instructions 8704 128 = true := by decide +kernel

theorem checked_8832 : checkChunk context facts instructions 8832 128 = true := by decide +kernel

theorem checked_8960 : checkChunk context facts instructions 8960 128 = true := by decide +kernel

theorem checked_9088 : checkChunk context facts instructions 9088 128 = true := by decide +kernel

theorem holds_block_8192 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 8192 → Holds H g ρ (facts n)) :
    ∀ n, n < 9216 → Holds H g ρ (facts n) := by
  have hall_8192 := checkChunk_sound valid facts instructions 8192 128 prior checked_8192
  have hall_8320 := checkChunk_sound valid facts instructions 8320 128 hall_8192 checked_8320
  have hall_8448 := checkChunk_sound valid facts instructions 8448 128 hall_8320 checked_8448
  have hall_8576 := checkChunk_sound valid facts instructions 8576 128 hall_8448 checked_8576
  have hall_8704 := checkChunk_sound valid facts instructions 8704 128 hall_8576 checked_8704
  have hall_8832 := checkChunk_sound valid facts instructions 8832 128 hall_8704 checked_8832
  have hall_8960 := checkChunk_sound valid facts instructions 8960 128 hall_8832 checked_8960
  have hall_9088 := checkChunk_sound valid facts instructions 9088 128 hall_8960 checked_9088
  exact hall_9088

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
