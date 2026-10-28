module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_31744 : checkChunk context facts instructions 31744 128 = true := by decide +kernel

theorem checked_31872 : checkChunk context facts instructions 31872 128 = true := by decide +kernel

theorem checked_32000 : checkChunk context facts instructions 32000 128 = true := by decide +kernel

theorem checked_32128 : checkChunk context facts instructions 32128 128 = true := by decide +kernel

theorem checked_32256 : checkChunk context facts instructions 32256 128 = true := by decide +kernel

theorem checked_32384 : checkChunk context facts instructions 32384 128 = true := by decide +kernel

theorem checked_32512 : checkChunk context facts instructions 32512 128 = true := by decide +kernel

theorem checked_32640 : checkChunk context facts instructions 32640 128 = true := by decide +kernel

theorem holds_block_31744 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 31744 → Holds H g ρ (facts n)) :
    ∀ n, n < 32768 → Holds H g ρ (facts n) := by
  have hall_31744 := checkChunk_sound valid facts instructions 31744 128 prior checked_31744
  have hall_31872 := checkChunk_sound valid facts instructions 31872 128 hall_31744 checked_31872
  have hall_32000 := checkChunk_sound valid facts instructions 32000 128 hall_31872 checked_32000
  have hall_32128 := checkChunk_sound valid facts instructions 32128 128 hall_32000 checked_32128
  have hall_32256 := checkChunk_sound valid facts instructions 32256 128 hall_32128 checked_32256
  have hall_32384 := checkChunk_sound valid facts instructions 32384 128 hall_32256 checked_32384
  have hall_32512 := checkChunk_sound valid facts instructions 32512 128 hall_32384 checked_32512
  have hall_32640 := checkChunk_sound valid facts instructions 32640 128 hall_32512 checked_32640
  exact hall_32640

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
