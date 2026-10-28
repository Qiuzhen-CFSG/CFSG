module

public import Theory.Representation.BinaryConjugationSection.OffenderIndex

/-!
# Fixed-index bounds on further sections

Passing to a section can only decrease the index of the image of a fixed
subgroup. Thus the original subgroup index proves the offender inequality
without requiring that fixed subgroup to contain the new coordinate kernel.
Source: Aschbacher--Smith13.7.12(3), printed p.942, plus-module application.
-/

public section

open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G D:Type*} [Group G] [Finite G] [Group D] [Finite D]
  {H U Z:Subgroup G} {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
/-- The fixed-index bound survives any quotient of the original module. -/
theorem offender_of_section_index
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
