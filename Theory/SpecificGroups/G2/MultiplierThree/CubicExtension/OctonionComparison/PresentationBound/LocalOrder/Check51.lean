module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_52224 : checkChunk context facts instructions 52224 128 = true := by decide +kernel

theorem checked_52352 : checkChunk context facts instructions 52352 128 = true := by decide +kernel

theorem checked_52480 : checkChunk context facts instructions 52480 128 = true := by decide +kernel

theorem checked_52608 : checkChunk context facts instructions 52608 128 = true := by decide +kernel

theorem checked_52736 : checkChunk context facts instructions 52736 128 = true := by decide +kernel

theorem checked_52864 : checkChunk context facts instructions 52864 128 = true := by decide +kernel

theorem checked_52992 : checkChunk context facts instructions 52992 128 = true := by decide +kernel

theorem checked_53120 : checkChunk context facts instructions 53120 128 = true := by decide +kernel

theorem holds_block_52224 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 52224 → Holds H g ρ (facts n)) :
    ∀ n, n < 53248 → Holds H g ρ (facts n) := by
  have hall_52224 := checkChunk_sound valid facts instructions 52224 128 prior checked_52224
  have hall_52352 := checkChunk_sound valid facts instructions 52352 128 hall_52224 checked_52352
  have hall_52480 := checkChunk_sound valid facts instructions 52480 128 hall_52352 checked_52480
  have hall_52608 := checkChunk_sound valid facts instructions 52608 128 hall_52480 checked_52608
  have hall_52736 := checkChunk_sound valid facts instructions 52736 128 hall_52608 checked_52736
  have hall_52864 := checkChunk_sound valid facts instructions 52864 128 hall_52736 checked_52864
  have hall_52992 := checkChunk_sound valid facts instructions 52992 128 hall_52864 checked_52992
  have hall_53120 := checkChunk_sound valid facts instructions 53120 128 hall_52992 checked_53120
  exact hall_53120

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
