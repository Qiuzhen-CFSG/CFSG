module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.Checking
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points

/-!
# Full coordinate domain for the witness action certificates

`Fin 3511` covers the published `Option (Fin 3510)` coordinates exactly. The
last index is `none`, whose Fi23 letter is 15181. The target is the unchanged
shared image table, with no correctness or bijectivity assumption.

The adjacent `Checks` modules compare this target with the already certified
literal witness actions from `Exhaustion.Geometry.Witness0` through `Witness7`.
Source: the retained `ImageData` relabeling and `source/images.g`;
application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation

/-- The proposed shared table action, including the extra coordinate. -/
def target (j : Fin 8) (i : Fin 3511) : Fin 31671 :=
  ImageData.point (Option.map (imageAction j) (finSuccEquivLast i))

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WitnessEvaluation
