module

public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.EndFieldTransfer

/-!
# Offenders from fixed subgroup indices

An actual centralizing subgroup supplies a fixed subspace. Its relative
index bounds the codimension of that fixed subspace, so comparison with
the original actor image order yields the offender inequality.
Source: Aschbacher--Smith13.7.12(3), printed p.942.
-/

public section

open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G D:Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H U Z:Subgroup G} {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
theorem offender_of_fixed_index
    (σ:Representation (ZMod 2) D W) (π:H→*D)
    (c:BinaryConjugationSection H U Z (σ.comp π))
    (A C:Subgroup G) (hC:C≤U) (hZC:Z≤C)
    (hAC:⁅A,C⁆=⊥)
    (hEA:IsElementaryTwo ((A.subgroupOf H).map π))
    (hi:C.relIndex U≤Nat.card ((A.subgroupOf H).map π)) :
    IsOffender σ ((A.subgroupOf H).map π) := by
  let :Finite W:=Finite.of_surjective (fun u:U=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hfix:c.imageSpace C≤fixedSpace σ ((A.subgroupOf H).map π) := by
    intro w hw a
    obtain ⟨aH,ha,he⟩:=a.property
    change σ (a:D) w=w
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le A C (hAC.le.trans bot_le) aH ha w hw
  have hcard:Nat.card W=Z.relIndex U := by
    let :=c.kernel_normal
    exact (Nat.card_congr c.quotientEquiv.toEquiv).symm
  have hc:Nat.card (c.imageSpace C)*C.relIndex U=Nat.card W := by
    rw [c.imageSpace_card_eq_relIndex C hC,hcard]
    exact relIndex_mul_relIndex Z C U hZC hC
  apply (BinaryOffender.EndFieldTransfer.offender_iff_card σ _ hEA).mpr
  calc
    Nat.card W=Nat.card (c.imageSpace C)*C.relIndex U:=hc.symm
    _≤Nat.card (fixedSpace σ ((A.subgroupOf H).map π))*Nat.card ((A.subgroupOf H).map π):=
      Nat.mul_le_mul (Nat.card_le_card_of_injective (Submodule.inclusion hfix) (Submodule.inclusion_injective hfix)) hi
    _=Nat.card ((A.subgroupOf H).map π)*Nat.card (fixedSpace σ ((A.subgroupOf H).map π)):=Nat.mul_comm _ _
end Representation.BinaryConjugationSection
