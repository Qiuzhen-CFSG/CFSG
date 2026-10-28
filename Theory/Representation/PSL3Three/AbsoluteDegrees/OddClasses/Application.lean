module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.OddClasses
public import Theory.Representation.PSL3Three.AbsoluteDegrees

/-!
# Supplying the native odd-class bound to the absolute-degree consumer

The matrix certificate discharges the conjugacy-class premise of the existing
small-degree saturation argument. The independent constructions of the simple
models remain explicit and belong to the degree-window assembly owner.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10.
-/

namespace Representation.PSL3Three.AbsoluteDegrees
universe v

/-- The independent simple-model constructions now suffice for the native
absolute-degree window: the odd-class premise is discharged by matrix certificates. -/
public theorem absoluteDegreeWindow_of_models
    (hprincipal : PrincipalModelsExist.{v}) (hsixteen : SixteenModelsExist.{v}) :
    AbsoluteDegreeWindow.{v} :=
  absoluteDegreeWindow_of_constructions hprincipal hsixteen
    Matrix.PSL3Three.odd_conjClasses_card_le_seven

end Representation.PSL3Three.AbsoluteDegrees
