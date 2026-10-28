module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ExtraspecialAction.Source
public import Theory.LinearAlgebra.BinaryLagrangianDualPair.Action

/-!
# The literal paired coordinates of the selected partner

This output record retains the actual E/Z subspace, the complete X action,
and the action of the originally selected element t. Its constructors use
the polar form and the two singular subgroups; its consumers identify the
fixed line, extraspecial actor, and final three-dimensional marking.
Source: Aschbacher--Smith, original 15.3.56(4--7), printed p.1148.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedCoordinates
open Recognition LocalRestrictions BinaryPairedTransvections
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

abbrev ESpace (y : G) := vectorSubspace Z ZS (intersectionE Z ZS y)

abbrev actor (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z))
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (b : Space Z ZS ≃ₗ[ZMod 2] PairedSpace E) :=
  BinaryLagrangianDualPair.coordinateActor (W := PairedSpace E) (actorRepresentation Z ZS hk) b

/-- The concrete output of the polar coordinate construction, with no
classification or model-image assumption left to its consumers. -/
structure Data (V₀ : Subgroup G) (y : G) (t : centralizerH Z)
    (hk : (quotientAction Z ZS).ker=pCore 2 (centralizerH Z)) where
  coordinates : Space Z ZS ≃ₗ[ZMod 2] PairedSpace (ESpace Z ZS y)
  centerVector : ESpace Z ZS y
  center_ne_zero : centerVector≠0
  axisForm : Module.Dual (ZMod 2) (ESpace Z ZS y)
  axis_ne_zero : axisForm≠0
  incident : axisForm centerVector=0
  E_image : ∀w:Space Z ZS,w∈vectorSubspace Z ZS (intersectionE Z ZS y) ↔
    (coordinates w).2=0
  Et_image : ∀w:Space Z ZS,w∈vectorSubspace Z ZS (rightConjugate (intersectionE Z ZS y) (t:G)) ↔
    (coordinates w).1=0
  center_image : ∀w:Space Z ZS,w∈vectorSubspace Z ZS V₀ ↔
    ∃a:ZMod 2,coordinates w=(a • centerVector,0)
  X_le_H : partnerX Z ZS y≤centralizerH Z
  parameter : partnerX Z ZS y →* centerGroup centerVector
  full : Function.Surjective parameter
  equivariant : ∀ (x:partnerX Z ZS y) (w:VectorQuotient Z ZS),
    coordinates (Additive.ofMul (quotientAction Z ZS ⟨x,X_le_H x.property⟩ w))=
      pairedAction (parameter x).val (coordinates (Additive.ofMul w))
  actor_image : (actorImage Z (partnerX Z ZS y)).map (actor Z ZS hk coordinates)=
    (centerGroup centerVector).map pairedAction
  quadratic_invariant : ∀a:ActorQuotient Z,∀w,
    BinaryNaturalDual.quadratic (actor Z ZS hk coordinates a w)=BinaryNaturalDual.quadratic w
  exchange_E : ∀v:ESpace Z ZS y,
    (actor Z ZS hk coordinates (QuotientGroup.mk' _ t) (v,0)).1=0
  exchange_D : ∀f:Module.Dual (ZMod 2) (ESpace Z ZS y),
    (actor Z ZS hk coordinates (QuotientGroup.mk' _ t) (0,f)).2=0
  exchange_center : actor Z ZS hk coordinates (QuotientGroup.mk' _ t) (centerVector,0)=(0,axisForm)
  exchange_axis : actor Z ZS hk coordinates (QuotientGroup.mk' _ t) (0,axisForm)=(centerVector,0)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedCoordinates
