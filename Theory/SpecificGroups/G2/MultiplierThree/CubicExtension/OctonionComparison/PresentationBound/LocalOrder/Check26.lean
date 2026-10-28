module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_26624 : checkChunk context facts instructions 26624 128 = true := by decide +kernel

theorem checked_26752 : checkChunk context facts instructions 26752 128 = true := by decide +kernel

theorem checked_26880 : checkChunk context facts instructions 26880 128 = true := by decide +kernel

theorem checked_27008 : checkChunk context facts instructions 27008 128 = true := by decide +kernel

theorem checked_27136 : checkChunk context facts instructions 27136 128 = true := by decide +kernel

theorem checked_27264 : checkChunk context facts instructions 27264 128 = true := by decide +kernel

theorem checked_27392 : checkChunk context facts instructions 27392 128 = true := by decide +kernel

theorem checked_27520 : checkChunk context facts instructions 27520 128 = true := by decide +kernel

theorem holds_block_26624 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 26624 → Holds H g ρ (facts n)) :
    ∀ n, n < 27648 → Holds H g ρ (facts n) := by
  have hall_26624 := checkChunk_sound valid facts instructions 26624 128 prior checked_26624
  have hall_26752 := checkChunk_sound valid facts instructions 26752 128 hall_26624 checked_26752
  have hall_26880 := checkChunk_sound valid facts instructions 26880 128 hall_26752 checked_26880
  have hall_27008 := checkChunk_sound valid facts instructions 27008 128 hall_26880 checked_27008
  have hall_27136 := checkChunk_sound valid facts instructions 27136 128 hall_27008 checked_27136
  have hall_27264 := checkChunk_sound valid facts instructions 27264 128 hall_27136 checked_27264
  have hall_27392 := checkChunk_sound valid facts instructions 27392 128 hall_27264 checked_27392
  have hall_27520 := checkChunk_sound valid facts instructions 27520 128 hall_27392 checked_27520
  exact hall_27520

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
