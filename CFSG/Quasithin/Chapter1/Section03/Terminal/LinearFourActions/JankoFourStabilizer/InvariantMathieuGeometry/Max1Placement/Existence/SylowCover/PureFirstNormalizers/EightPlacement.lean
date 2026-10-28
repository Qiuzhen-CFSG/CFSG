module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CensusApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightPlacement

/-!
# The pure-first exceptional endpoint with its native input discharged

The actual native eight-normalizer theorem supplies the independent placement
premise of the source endpoint. The original whole normalizer, its pure
witness, and the literal full-centralizer conjugation are retained.
Source: Kleidman--Wilson (1988), §2.1, pp.488–489.
-/
public noncomputable section
namespace Janko4.LocalStructure.PureFirstNormalizers
open Subgroup ElementaryNormalizerCover

/-- The exceptional pure-first source branch reaches the actual F local without
an additional eight-normalizer placement hypothesis. -/
theorem source_pure_exceptional_endpoint_native
    (X Z : Subgroup Model) (g : Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model))
    (hC : (centralizer (Z : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1) :
    ∃ k : Model, normalizer (X : Set Model) =
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom :=
  source_pure_exceptional_endpoint PureTwoA.eightNormalizerPlacement X Z g hmax hNZ hC

end Janko4.LocalStructure.PureFirstNormalizers
