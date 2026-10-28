module
public import Theory.Representation.BinaryConjugationSection.OffenderQuotientIndex

/-!
# Offenders on finite sections in an arbitrary ambient group

The image of a subgroup with kernel-valued displacement lies in the fixed
space. Its relative index bounds the fixed codimension. Only the subgroup
above the section must be finite; the ambient free-amalgam group need not be.
This retains the actual coordinate and actor maps.

Source: the fixed-index criterion of Aschbacher--Smith13.7.12(3), printed p.942,
applied to the paired secondary orbits in MS93 (3.6), printed p.871.
-/

public section

open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G D:Type*} [Group G] [Group D] [Finite D]
  {H U Z:Subgroup G} {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
/-- The fixed-index criterion needs only finiteness of the subgroup above
the section, even in an infinite ambient group. -/
theorem offender_of_section_index_of_finite [Finite U]
    (σ:Representation (ZMod 2) D W) (π:H→*D)
    (c:BinaryConjugationSection H U Z (σ.comp π))
    (A C:Subgroup G) (hAC:⁅A,C⁆≤Z)
    (hEA:IsElementaryTwo ((A.subgroupOf H).map π))
    (hi:C.relIndex U≤Nat.card ((A.subgroupOf H).map π)) :
    IsOffender σ ((A.subgroupOf H).map π) := by
  let :Finite W:=Finite.of_surjective (fun u:U=>(c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let Ci:Subgroup (Multiplicative W):=(C.subgroupOf U).map c.coordinates
  have hfix:c.imageSpace C≤fixedSpace σ ((A.subgroupOf H).map π) := by
    intro w hw a
    obtain ⟨aH,ha,he⟩:=a.property
    change σ (a:D) w=w
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le A C hAC aH ha w hw
  have hidx:Ci.index≤C.relIndex U:=Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf U).index_map_dvd c.onto)
  have hcard:Nat.card (c.imageSpace C)*Ci.index=Nat.card W:=Ci.card_mul_index
  apply (BinaryOffender.EndFieldTransfer.offender_iff_card σ _ hEA).mpr
  calc
    Nat.card W=Nat.card (c.imageSpace C)*Ci.index:=hcard.symm
    _≤Nat.card (fixedSpace σ ((A.subgroupOf H).map π))*Nat.card ((A.subgroupOf H).map π):=
      Nat.mul_le_mul (Nat.card_le_card_of_injective (Submodule.inclusion hfix) (Submodule.inclusion_injective hfix)) (hidx.trans hi)
    _=Nat.card ((A.subgroupOf H).map π)*Nat.card (fixedSpace σ ((A.subgroupOf H).map π)):=Nat.mul_comm _ _
end Representation.BinaryConjugationSection
