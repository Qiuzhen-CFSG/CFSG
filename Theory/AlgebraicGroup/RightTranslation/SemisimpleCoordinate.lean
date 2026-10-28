module

public import Theory.AlgebraicGroup.RightTranslation.Representation

universe u

/-! Semisimple elements in the faithful coordinate-translation representation. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- An intrinsically semisimple element acts semisimply on the finite
coordinate-translation submodule. -/
public theorem rightTranslationOnCoordinateSubmodule_isSemisimple
    {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G) (hg : IsSemisimpleElement G g) :
    Module.End.IsSemisimple
      (rightTranslationOnCoordinateSubmodule G g) := by
  let R : Module.End k (Variety.PolynomialFunction G) :=
    rightTranslationPullback G g
  have hInv : coordinateTranslationSubmodule G ∈ R.invtSubmodule :=
    coordinateTranslationSubmodule_mapsTo G g
  have h := hg (coordinateTranslationSubmodule G) hInv
    (coordinateTranslationSubmodule_finite G)
  simpa [R, rightTranslationOnCoordinateSubmodule, LinearMap.restrict] using h

end Theory.AlgebraicGroup
