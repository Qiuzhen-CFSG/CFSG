module

public import Theory.AlgebraicGroup.Bor1.ChevalleyWeightRestriction
public import Theory.AlgebraicGroup.Bor1.WeightLinePointKernel

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped ExteriorAlgebra
variable {k : Type u} [Field k]

/-- The common `H`-weight blocks inside the Chevalley common-weight span. -/
public noncomputable def chevalleyCommonWeightBlock
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (χ : Representation.commonWeightIndex
      (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup) :
    Submodule k (chevalleyCommonWeightSpan H) :=
  Representation.commonWeightBlock
    (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup χ

/-- Normal conjugation permutes the common Chevalley weight blocks. -/
public noncomputable def chevalleyCommonWeightPermutation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    Variety.Point G →* Equiv.Perm
      (Representation.commonWeightIndex
        (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup) := by
  let _ : H.toSubgroup.Normal := hN
  exact Representation.normalCommonWeightPermutation
    (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup

/-- The restricted Chevalley action transports each named weight block along
the named normal-conjugation permutation. -/
public theorem chevalleyCommonWeightBlock_map_of_restriction
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (τ : RationalRepresentation G (chevalleyCommonWeightSpan H))
    (hτ : IsRestrictionRepresentation
      H.rightTranslateVanishingExteriorRationalRepresentation
      (chevalleyCommonWeightSpan H) τ) (g : Variety.Point G)
    (χ : Representation.commonWeightIndex
      (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup) :
    Submodule.map (τ.action g : Module.End k (chevalleyCommonWeightSpan H))
        (chevalleyCommonWeightBlock H χ) =
      chevalleyCommonWeightBlock H
        (chevalleyCommonWeightPermutation H hN g χ) := by
  let _ : H.toSubgroup.Normal := hN
  exact Representation.commonWeightBlock_map_of_restriction
    (chevalleyExteriorUnderlyingRepresentation H) H.toSubgroup τ.action hτ g χ

end Theory.AlgebraicGroup.Bor1
