module

public import Theory.AlgebraicGroup.Bor1.WeightSpacePermutation
public import Theory.AlgebraicGroup.RightTranslation.ExteriorRational

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The abstract point-group representation underlying the rational Chevalley
exterior representation. -/
@[expose]
public noncomputable def chevalleyExteriorUnderlyingRepresentation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Representation k (Variety.Point G)
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
  rationalRepresentationUnderlying
    H.rightTranslateVanishingExteriorRationalRepresentation

/-- The sum of the nonzero common `H`-weight spaces in the Chevalley exterior
representation. -/
@[expose]
public noncomputable def chevalleyCommonWeightSpan
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Submodule k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
  Representation.commonWeightSpan
    (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup

/-- The Chevalley exterior representation restricts rationally to the sum of
its nonzero common weight spaces for a normal closed subgroup. -/
public theorem ClosedSubgroup.exists_chevalleyCommonWeightRestriction
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ τ : RationalRepresentation G (chevalleyCommonWeightSpan H),
      IsRestrictionRepresentation
          H.rightTranslateVanishingExteriorRationalRepresentation
          (chevalleyCommonWeightSpan H) τ ∧
        IsRationalRepresentation τ := by
  let _ : H.toSubgroup.Normal := hN
  let ρ := H.rightTranslateVanishingExteriorRationalRepresentation
  let F := chevalleyCommonWeightSpan H
  exact rationalRepresentation_restriction_exists
    ρ H.rightTranslateVanishingExteriorRationalRepresentation_isRational F
    (RationalRepresentation.commonWeightSpan_isInvariantSubmodule
      ρ H.toSubgroup)

end Theory.AlgebraicGroup.Bor1
