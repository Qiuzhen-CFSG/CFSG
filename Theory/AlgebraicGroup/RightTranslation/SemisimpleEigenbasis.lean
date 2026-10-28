module

public import Theory.AlgebraicGroup.Representations.Semisimple
public import Theory.AlgebraicGroup.RightTranslation.SemisimpleCoordinate

universe u

/-! Eigenbases for semisimple elements in the faithful coordinate-translation
representation. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A semisimple element acts diagonally in some finite basis of the faithful
coordinate-translation representation. -/
public theorem exists_coordinateTranslation_eigenbasis
    {G : Variety k} [AlgebraicGroup G]
    (g : Variety.Point G) (hg : IsSemisimpleElement G g) :
    ∃ (b : Module.Basis (Fin (Module.finrank k
        (coordinateTranslationSubmodule G))) k
        (coordinateTranslationSubmodule G))
      (μ : Fin (Module.finrank k (coordinateTranslationSubmodule G)) → k),
      ∀ i, rightTranslationOnCoordinateSubmodule G g (b i) =
        μ i • b i := by
  let : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  exact Module.End.IsSemisimple.exists_fin_eigenbasis
    (rightTranslationOnCoordinateSubmodule G g)
    (rightTranslationOnCoordinateSubmodule_isSemisimple g hg)

end Theory.AlgebraicGroup
