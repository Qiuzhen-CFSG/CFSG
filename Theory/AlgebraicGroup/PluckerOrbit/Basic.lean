module

public import Theory.AlgebraicGroup.RightTranslation.Orbit

universe u

/-! The exterior representation restricted to the affine Plücker orbit span. -/

namespace Theory.AlgebraicGroup

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanGeneralLinear
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Point G →*
      LinearMap.GeneralLinearGroup k
        H.rightTranslateVanishingPluckerOrbitSpan :=
  linearRepresentationRestrict
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerOrbitSpan
    H.rightTranslateVanishingPluckerOrbitSpan_stable

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanGeneralLinear_apply_coe
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) (x : H.rightTranslateVanishingPluckerOrbitSpan) :
    (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
      LinearMap.GeneralLinearGroup k
        H.rightTranslateVanishingPluckerOrbitSpan) :
      Module.End k H.rightTranslateVanishingPluckerOrbitSpan) x :
        ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan) =
      ((H.rightTranslateVanishingExteriorGeneralLinear g :
        LinearMap.GeneralLinearGroup k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) :
        Module.End k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) x :=
  linearRepresentationRestrict_apply_coe
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerOrbitSpan
    H.rightTranslateVanishingPluckerOrbitSpan_stable g x

end

/-! The ambient coordinate extension agrees with restricted coordinates on the orbit span. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension_restricted_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
    (g : Variety.Point G)
    (x : H.rightTranslateVanishingPluckerOrbitSpan) :
    H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i
        (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
          Module.End k H.rightTranslateVanishingPluckerOrbitSpan) x :
          ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan) =
      H.rightTranslateVanishingPluckerOrbitSpanBasis.repr
        (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
          Module.End k H.rightTranslateVanishingPluckerOrbitSpan) x) i := by
  exact H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension_apply i
    (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
      LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
      Module.End k H.rightTranslateVanishingPluckerOrbitSpan) x)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension_restricted_eq_ambient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan))
    (g : Variety.Point G)
    (x : H.rightTranslateVanishingPluckerOrbitSpan) :
    H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i
        (((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
          LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
          Module.End k H.rightTranslateVanishingPluckerOrbitSpan) x :
          ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan) =
      H.rightTranslateVanishingPluckerOrbitSpanCoordinateExtension i
        (((H.rightTranslateVanishingExteriorGeneralLinear g :
          LinearMap.GeneralLinearGroup k _) : Module.End k _)
          (x : ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) := by
  congr 1

end

end Theory.AlgebraicGroup
