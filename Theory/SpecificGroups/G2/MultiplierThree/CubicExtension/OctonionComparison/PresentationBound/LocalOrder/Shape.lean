module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck00
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck01
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck02
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck03
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck04
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck05
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck06
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck07
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck08
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck09
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.ShapeCheck10

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2/MultiplierThree/CubicExtension/OctonionComparison/PresentationBound/LocalOrder/source/Generate.py`.
Source: the seven literal local words; see `../source/README.md`. -/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
open Subgroup.CosetWordCertificate

/-- Every selected final fact has the requested signed letter and endpoints. -/
theorem hshape : ∀ i a, facts (output i a) =
    ⟨survivor i, [a], survivor (dest i a)⟩ := by
  intro i
  by_cases h0 : i.val < 128
  · exact shapeChunk_sound 0 128 shape_checked_0 i (by omega) h0
  by_cases h128 : i.val < 256
  · exact shapeChunk_sound 128 128 shape_checked_128 i (by omega) h128
  by_cases h256 : i.val < 384
  · exact shapeChunk_sound 256 128 shape_checked_256 i (by omega) h256
  by_cases h384 : i.val < 512
  · exact shapeChunk_sound 384 128 shape_checked_384 i (by omega) h384
  by_cases h512 : i.val < 640
  · exact shapeChunk_sound 512 128 shape_checked_512 i (by omega) h512
  by_cases h640 : i.val < 768
  · exact shapeChunk_sound 640 128 shape_checked_640 i (by omega) h640
  by_cases h768 : i.val < 896
  · exact shapeChunk_sound 768 128 shape_checked_768 i (by omega) h768
  by_cases h896 : i.val < 1024
  · exact shapeChunk_sound 896 128 shape_checked_896 i (by omega) h896
  by_cases h1024 : i.val < 1152
  · exact shapeChunk_sound 1024 128 shape_checked_1024 i (by omega) h1024
  by_cases h1152 : i.val < 1280
  · exact shapeChunk_sound 1152 128 shape_checked_1152 i (by omega) h1152
  exact shapeChunk_sound 1280 16 shape_checked_1280 i (by omega) i.isLt

theorem hlt : ∀ i a, output i a < 85576 := by
  intro i a
  exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
