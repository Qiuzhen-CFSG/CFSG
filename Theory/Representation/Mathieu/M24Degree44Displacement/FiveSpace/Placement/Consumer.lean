module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace

/-!
# Application of the binary placement reduction to fixed spaces

The completeness and scalar-descent argument supplies exactly the placement
premise of `fiveFixedSpaceBound_of_golay_exterior`. The independent exterior
fixed-space calculation remains an explicit premise of this application.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17.
-/

public section
namespace Representation.MathieuM24Degree44
open FiveSpace Placement Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
universe v

/-- The actual fixed-space consumer, keeping all unfinished concrete
construction premises explicit. -/
theorem fiveFixedSpaceBound_of_binary_section_models
    (hsmall : BinarySectionModels) (hlarge : LargeModelsExist.{v})
    (hclasses : OddClassBound) (hexterior : GolayExteriorFiveBound) :
    FiveFixedSpaceBound.{v} :=
  fiveFixedSpaceBound_of_golay_exterior
    (golayExteriorPlacement_of_binary_models hsmall hlarge hclasses) hexterior

end Representation.MathieuM24Degree44
