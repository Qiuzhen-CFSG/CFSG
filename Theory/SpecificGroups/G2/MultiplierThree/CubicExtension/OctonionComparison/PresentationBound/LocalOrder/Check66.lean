module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_67584 : checkChunk context facts instructions 67584 128 = true := by decide +kernel

theorem checked_67712 : checkChunk context facts instructions 67712 128 = true := by decide +kernel

theorem checked_67840 : checkChunk context facts instructions 67840 128 = true := by decide +kernel

theorem checked_67968 : checkChunk context facts instructions 67968 128 = true := by decide +kernel

theorem checked_68096 : checkChunk context facts instructions 68096 128 = true := by decide +kernel

theorem checked_68224 : checkChunk context facts instructions 68224 128 = true := by decide +kernel

theorem checked_68352 : checkChunk context facts instructions 68352 128 = true := by decide +kernel

theorem checked_68480 : checkChunk context facts instructions 68480 128 = true := by decide +kernel

theorem holds_block_67584 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 67584 → Holds H g ρ (facts n)) :
    ∀ n, n < 68608 → Holds H g ρ (facts n) := by
  have hall_67584 := checkChunk_sound valid facts instructions 67584 128 prior checked_67584
  have hall_67712 := checkChunk_sound valid facts instructions 67712 128 hall_67584 checked_67712
  have hall_67840 := checkChunk_sound valid facts instructions 67840 128 hall_67712 checked_67840
  have hall_67968 := checkChunk_sound valid facts instructions 67968 128 hall_67840 checked_67968
  have hall_68096 := checkChunk_sound valid facts instructions 68096 128 hall_67968 checked_68096
  have hall_68224 := checkChunk_sound valid facts instructions 68224 128 hall_68096 checked_68224
  have hall_68352 := checkChunk_sound valid facts instructions 68352 128 hall_68224 checked_68352
  have hall_68480 := checkChunk_sound valid facts instructions 68480 128 hall_68352 checked_68480
  exact hall_68480

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
