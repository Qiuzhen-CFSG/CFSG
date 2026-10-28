module

public import Theory.AlgebraicGroup.Bor1.ChevalleyExteriorDifferential
public import Theory.AlgebraicGroup.RightTranslation.ExteriorRational

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The differential of the rational Chevalley exterior representation on
the Pluecker vector is the explicit exterior-minor differential. -/
public theorem ClosedSubgroup.rationalRepresentationDifferential_plucker_eq_chevalleyExterior
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (b : Module.Basis
      (Fin (Module.finrank k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan))) k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan))
    (f : AlgebraicGroup.Morphism G
      (glVarietyOf k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)))
    (hf : ∀ g, glPointEquivOf k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) b (f.onPoints g) =
      H.rightTranslateVanishingExteriorRationalRepresentation.action g)
    (D : IdentityPointDerivation G) :
    rationalRepresentationDifferential
        H.rightTranslateVanishingExteriorRationalRepresentation b f D
        H.rightTranslateVanishingPluckerVector =
      ClosedSubgroup.chevalleyExteriorWedgeDifferential H D := by
  apply b.ext_elem
  intro i
  change b.coord i
      (rationalRepresentationDifferential
        H.rightTranslateVanishingExteriorRationalRepresentation b f D
          H.rightTranslateVanishingPluckerVector) =
    b.coord i (ClosedSubgroup.chevalleyExteriorWedgeDifferential H D)
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  rw [ClosedSubgroup.chevalleyExteriorWedgeDifferential]
  rw [rationalRepresentationExteriorWedgeDifferential_coefficient]
  congr 1
  apply Variety.PolynomialFunction.ext
  intro g
  rw [rationalRepresentationLinearMatrixCoefficient_apply
    H.rightTranslateVanishingExteriorRationalRepresentation b f hf]
  rw [rationalRepresentationExteriorWedgeCoefficient_apply]
  · let T := exteriorPower.map
      H.rightTranslateVanishingTopWedgeData.degree
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        (H.rightTranslateVanishingSpanGeneralLinear g)).toLinearMap
    change b.coord i (T H.rightTranslateVanishingPluckerVector) =
      b.coord i (T (exteriorPower.ιMulti k
        H.rightTranslateVanishingTopWedgeData.degree
        (fun j => ClosedSubgroup.chevalleyAdaptedBasis H
          (ClosedSubgroup.chevalleyAdaptedIndex H j))))
    exact congrArg (fun z => b.coord i (T z))
      (ClosedSubgroup.chevalleyAdaptedTopWedge_eq_plucker H).symm
  · exact ClosedSubgroup.rightTranslateVanishingRepresentationMorphismOfBasis_pointEquiv
      H (ClosedSubgroup.chevalleyAdaptedBasis H)

end Theory.AlgebraicGroup.Bor1
