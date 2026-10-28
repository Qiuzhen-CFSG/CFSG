module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.factsTable
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.instructionsTable

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

theorem checked_0 : checkChunk context facts instructions 0 128 = true := by decide +kernel

theorem checked_128 : checkChunk context facts instructions 128 128 = true := by decide +kernel

theorem checked_256 : checkChunk context facts instructions 256 128 = true := by decide +kernel

theorem checked_384 : checkChunk context facts instructions 384 128 = true := by decide +kernel

theorem checked_512 : checkChunk context facts instructions 512 128 = true := by decide +kernel

theorem checked_640 : checkChunk context facts instructions 640 128 = true := by decide +kernel

theorem checked_768 : checkChunk context facts instructions 768 128 = true := by decide +kernel

theorem checked_896 : checkChunk context facts instructions 896 128 = true := by decide +kernel

theorem holds_block_0 {G : Type*} [Group G] {H : Subgroup G}
    {g : Bool → G} {ρ : Nat → G}
    (valid : Valid context H g ρ)
    (prior : ∀ n, n < 0 → Holds H g ρ (facts n)) :
    ∀ n, n < 1024 → Holds H g ρ (facts n) := by
  have hall_0 := checkChunk_sound valid facts instructions 0 128 prior checked_0
  have hall_128 := checkChunk_sound valid facts instructions 128 128 hall_0 checked_128
  have hall_256 := checkChunk_sound valid facts instructions 256 128 hall_128 checked_256
  have hall_384 := checkChunk_sound valid facts instructions 384 128 hall_256 checked_384
  have hall_512 := checkChunk_sound valid facts instructions 512 128 hall_384 checked_512
  have hall_640 := checkChunk_sound valid facts instructions 640 128 hall_512 checked_640
  have hall_768 := checkChunk_sound valid facts instructions 768 128 hall_640 checked_768
  have hall_896 := checkChunk_sound valid facts instructions 896 128 hall_768 checked_896
  exact hall_896

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
