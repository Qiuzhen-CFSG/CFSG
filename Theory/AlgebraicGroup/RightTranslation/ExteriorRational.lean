module

public import Theory.AlgebraicGroup.Representations.Operations
public import Theory.AlgebraicGroup.RightTranslation.Exterior

universe u

namespace Theory.AlgebraicGroup

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The Chevalley exterior-power point action, packaged as a rational
representation. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingExteriorRationalRepresentation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    RationalRepresentation G
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
  ⟨H.rightTranslateVanishingExteriorGeneralLinear⟩

/-- The Chevalley exterior-power representation is rational. -/
public theorem ClosedSubgroup.rightTranslateVanishingExteriorRationalRepresentation_isRational
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IsRationalRepresentation
      H.rightTranslateVanishingExteriorRationalRepresentation := by
  let E := ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
    H.rightTranslateVanishingSpan
  let b : Module.Basis (Fin (Module.finrank k E)) k E := Module.finBasis k E
  let c : Fin (Module.finrank k E) → Fin (Module.finrank k E) →
      G.PolynomialFunction := fun i j =>
    H.rightTranslateVanishingExteriorLinearMatrixCoefficient (b.coord i) (b j)
  let cInv : Fin (Module.finrank k E) → Fin (Module.finrank k E) →
      G.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G) (c i j)
  have hc : ∀ i j g, c i j g =
      b.repr ((H.rightTranslateVanishingExteriorGeneralLinear g : Module.End k E)
        (b j)) i := by
    intro i j g
    exact H.rightTranslateVanishingExteriorLinearMatrixCoefficient_apply
      (b.coord i) (b j) g
  have hcInv : ∀ i j g, cInv i j g =
      b.repr (((((H.rightTranslateVanishingExteriorGeneralLinear g)⁻¹ :
        LinearMap.GeneralLinearGroup k E) : Module.End k E)) (b j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b H.rightTranslateVanishingExteriorGeneralLinear c cInv hc hcInv
  refine ⟨b, f, ?_⟩
  intro g
  change glPointEquivOf k E b
    (generalLinearRepresentationPoint b
      (H.rightTranslateVanishingExteriorGeneralLinear g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint b
    (H.rightTranslateVanishingExteriorGeneralLinear g)

end Theory.AlgebraicGroup
