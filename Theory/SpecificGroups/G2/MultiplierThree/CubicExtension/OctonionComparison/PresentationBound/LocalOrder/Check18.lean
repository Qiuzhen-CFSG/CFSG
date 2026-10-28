module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_18432 : checkChunk context facts instructions 18432 128 = true := by decide +kernel

theorem checked_18560 : checkChunk context facts instructions 18560 128 = true := by decide +kernel

theorem checked_18688 : checkChunk context facts instructions 18688 128 = true := by decide +kernel

theorem checked_18816 : checkChunk context facts instructions 18816 128 = true := by decide +kernel

theorem checked_18944 : checkChunk context facts instructions 18944 128 = true := by decide +kernel

theorem checked_19072 : checkChunk context facts instructions 19072 128 = true := by decide +kernel

theorem checked_19200 : checkChunk context facts instructions 19200 128 = true := by decide +kernel

theorem checked_19328 : checkChunk context facts instructions 19328 128 = true := by decide +kernel

theorem holds_block_18432 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 18432 → Holds H g ρ (facts n)) :
    ∀ n, n < 19456 → Holds H g ρ (facts n) := by
  have hall_18432 := checkChunk_sound valid facts instructions 18432 128 prior checked_18432
  have hall_18560 := checkChunk_sound valid facts instructions 18560 128 hall_18432 checked_18560
  have hall_18688 := checkChunk_sound valid facts instructions 18688 128 hall_18560 checked_18688
  have hall_18816 := checkChunk_sound valid facts instructions 18816 128 hall_18688 checked_18816
  have hall_18944 := checkChunk_sound valid facts instructions 18944 128 hall_18816 checked_18944
  have hall_19072 := checkChunk_sound valid facts instructions 19072 128 hall_18944 checked_19072
  have hall_19200 := checkChunk_sound valid facts instructions 19200 128 hall_19072 checked_19200
  have hall_19328 := checkChunk_sound valid facts instructions 19328 128 hall_19200 checked_19328
  exact hall_19328

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
