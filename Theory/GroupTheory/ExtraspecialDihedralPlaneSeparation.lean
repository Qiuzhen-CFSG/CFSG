module

public import Theory.GroupTheory.ExtraspecialDihedralElementaryOverlap

/-!
# Distinct plane intersections with an extraspecial dihedral kernel

If two elementary subgroups generate an order256 subgroup, they cannot
meet the order128 extraspecial kernel in the same sixteen. Otherwise that
sixteen is centralized by their join; its self-centralizer inside the
kernel bounds the join-kernel intersection by16. The image in D8 bounds
that same intersection below by32.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

public theorem extraspecial_dihedral_plane_intersections_ne
    {S : Type*} [Group S] [Finite S] (π : S→*DihedralGroup 4)
    [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128)
    (U W : Subgroup S) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hU : Nat.card U=64) (hjoin : Nat.card (U⊔W : Subgroup S)=256) :
    (U⊓π.ker : Subgroup S)≠W⊓π.ker := by
  obtain ⟨hI,_,_,hCA⟩ := extraspecial_dihedral_elementary_overlap π hP U hU
  intro he
  have hR : U⊔W≤centralizer (U⊓π.ker : Set S) := by
    apply sup_le
    · exact U.le_centralizer.trans (centralizer_le inf_le_left)
    · change W≤centralizer ((U⊓π.ker : Subgroup S) : Set S)
      rw [he]
      exact W.le_centralizer.trans (centralizer_le inf_le_left)
  have hle : (U⊔W)⊓π.ker≤U⊓π.ker := by
    intro x hx
    have hh : (⟨x,hx.2⟩:π.ker)∈centralizer (U.subgroupOf π.ker : Set π.ker) := by
      intro y hy
      exact Subtype.ext (hR hx.1 y.val ⟨hy,y.property⟩)
    rw [hCA] at hh
    exact ⟨hh,hx.2⟩
  have hbound : Nat.card ((U⊔W)⊓π.ker : Subgroup S)≤16 := hI ▸ card_le_of_le hle
  have himage : Nat.card ((U⊔W).map π)≤8 := by
    have hh := Nat.card_le_card_of_injective ((U⊔W).map π).subtype
      ((U⊔W).map π).subtype_injective
    simpa only [DihedralGroup.nat_card] using hh
  have hmul := IsElementaryAbelian.card_inf_ker_mul_card_map (U⊔W) π
  rw [hjoin] at hmul
  nlinarith

end Theory.GroupTheory
