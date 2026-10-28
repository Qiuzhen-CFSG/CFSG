module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_19456 : checkChunk context facts instructions 19456 128 = true := by decide +kernel

theorem checked_19584 : checkChunk context facts instructions 19584 128 = true := by decide +kernel

theorem checked_19712 : checkChunk context facts instructions 19712 128 = true := by decide +kernel

theorem checked_19840 : checkChunk context facts instructions 19840 128 = true := by decide +kernel

theorem checked_19968 : checkChunk context facts instructions 19968 128 = true := by decide +kernel

theorem checked_20096 : checkChunk context facts instructions 20096 128 = true := by decide +kernel

theorem checked_20224 : checkChunk context facts instructions 20224 128 = true := by decide +kernel

theorem checked_20352 : checkChunk context facts instructions 20352 128 = true := by decide +kernel

theorem holds_block_19456 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 19456 → Holds H g ρ (facts n)) :
    ∀ n, n < 20480 → Holds H g ρ (facts n) := by
  have hall_19456 := checkChunk_sound valid facts instructions 19456 128 prior checked_19456
  have hall_19584 := checkChunk_sound valid facts instructions 19584 128 hall_19456 checked_19584
  have hall_19712 := checkChunk_sound valid facts instructions 19712 128 hall_19584 checked_19712
  have hall_19840 := checkChunk_sound valid facts instructions 19840 128 hall_19712 checked_19840
  have hall_19968 := checkChunk_sound valid facts instructions 19968 128 hall_19840 checked_19968
  have hall_20096 := checkChunk_sound valid facts instructions 20096 128 hall_19968 checked_20096
  have hall_20224 := checkChunk_sound valid facts instructions 20224 128 hall_20096 checked_20224
  have hall_20352 := checkChunk_sound valid facts instructions 20352 128 hall_20224 checked_20352
  exact hall_20352

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
