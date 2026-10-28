module

public import Theory.SpecificGroups.Tits.SharpOuterBound.Kernel
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalRestrictions
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound

/-!
# Sharp counting for all Tits automorphisms

Sylow conjugacy makes the stabilizer of the certified Sylow subgroup
surject onto the full outer automorphism group. Its outer kernel contains
the 2048 distinct inner automorphisms induced by that Sylow subgroup.
The kernel of restriction to the Sylow subgroup has order at most two.
The certified local count bounds all compatible parabolic restrictions by
2048, hence also the image of global restriction. Combining these counts
proves the outer bound of two and the full automorphism bound of 35942400,
without additional mathematical premises. The bounds transfer to Parrott's
presented group through its certified isomorphism with the Atlas carrier.

Source: Aschbacher–Smith F.1.12, printed pp.263–264, and Parrott (1972),
§5, p.683. GLS3 2.5.15 alone only identifies two automorphism groups.
-/

namespace Tits.SharpOuterBound
open Subgroup OuterOddSubgroups

private theorem conj_injective :
    Function.Injective (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (MulAut.conj : Atlas1600Group →* MulAut Atlas1600Group).ker.eq_bot_iff_forall.mpr
  intro x hx
  have hx' : MulAut.conj x = 1 := hx
  have hz : x ∈ center Atlas1600Group := by
    rw [mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun hx' y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [RelativeSylowMarking.atlas_center_eq_bot, mem_bot] using hz

private theorem inner_preserves_sylow (s : atlas1600SylowTwoSubgroup) :
    atlas1600SylowTwoSubgroup.map (MulAut.conj s.val).toMonoidHom =
      atlas1600SylowTwoSubgroup := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact atlas1600SylowTwoSubgroup.mul_mem
      (atlas1600SylowTwoSubgroup.mul_mem s.property hx)
      (atlas1600SylowTwoSubgroup.inv_mem s.property)
  · rw [card_map_of_injective (MulAut.conj s.val).injective]

private def innerSylow (s : atlas1600SylowTwoSubgroup) : toOuter.ker :=
  ⟨⟨MulAut.conj s.val, inner_preserves_sylow s⟩, by
    change QuotientGroup.mk' (MulAut.innerSubgroup Atlas1600Group) (MulAut.conj s.val) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨s.val, rfl⟩⟩

private theorem innerSylow_injective : Function.Injective innerSylow := by
  intro s t h
  apply Subtype.ext
  apply conj_injective
  exact congrArg (fun a : toOuter.ker => a.val.val) h

/-- The kernel of the surjection to all outer classes contains 2048 inner maps. -/
public theorem toOuter_kernel_card_ge : 2048 ≤ Nat.card toOuter.ker := by
  rw [← atlas1600SylowTwoSubgroup_card]
  exact Nat.card_le_card_of_injective innerSylow innerSylow_injective

/-- Counting the restriction image bounds the entire Sylow stabilizer. -/
public theorem sylowStabilizer_card_le_of_range
    (himage : Nat.card sylowRestriction.range ≤ 2048) : Nat.card sylowStabilizer ≤ 4096 := by
  calc
    Nat.card sylowStabilizer = Nat.card sylowRestriction.ker * Nat.card sylowRestriction.range := by
      rw [← index_ker, card_mul_index]
    _ ≤ 2 * 2048 := Nat.mul_le_mul sylowRestriction_kernel_card_le_two himage
    _ = 4096 := by norm_num

/-- A bound on all extendible Sylow restrictions controls the actual outer quotient. -/
public theorem atlas_outer_card_le_two_of_restriction_range
    (himage : Nat.card sylowRestriction.range ≤ 2048) :
    Nat.card (MulAut.Outer Atlas1600Group) ≤ 2 := by
  have hcount : Nat.card toOuter.ker * Nat.card (MulAut.Outer Atlas1600Group) =
      Nat.card sylowStabilizer := by
    have he := toOuter.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr toOuter_surjective, card_top] at he
    exact he
  have hle := Nat.mul_le_mul_right (Nat.card (MulAut.Outer Atlas1600Group)) toOuter_kernel_card_ge
  rw [hcount] at hle
  have hs := sylowStabilizer_card_le_of_range himage
  omega

/-- The certified Parrott–Atlas isomorphism transports the sharp outer bound. -/
public theorem parrott_outer_card_le_two_of_restriction_range
    (himage : Nat.card sylowRestriction.range ≤ 2048) :
    Nat.card (MulAut.Outer ParrottGroup) ≤ 2 := by
  rw [Nat.card_congr (MulAut.outerCongr parrottFiniteImageEquiv).toEquiv]
  exact atlas_outer_card_le_two_of_restriction_range himage

/-- The same count bounds every automorphism of the presented group. -/
public theorem parrott_aut_card_le_of_restriction_range
    (himage : Nat.card sylowRestriction.range ≤ 2048) :
    Nat.card (MulAut ParrottGroup) ≤ 35942400 := by
  have hi : Nat.card (MulAut.innerSubgroup ParrottGroup) ≤ Nat.card ParrottGroup :=
    Nat.card_le_card_of_surjective _ (MulAut.conj : ParrottGroup →* MulAut ParrottGroup).rangeRestrict_surjective
  calc
    Nat.card (MulAut ParrottGroup) =
        Nat.card (MulAut.innerSubgroup ParrottGroup) * Nat.card (MulAut.Outer ParrottGroup) :=
      (MulAut.innerSubgroup ParrottGroup).card_mul_index.symm
    _ ≤ Nat.card ParrottGroup * 2 := Nat.mul_le_mul hi
      (parrott_outer_card_le_two_of_restriction_range himage)
    _ = 35942400 := by rw [parrottGroup_card]

/-- A count of compatible local restrictions suffices for the full outer bound. -/
public theorem parrott_outer_card_le_two_of_compatible
    (hlocal : Nat.card CompatibleSylowRestrictions ≤ 2048) :
    Nat.card (MulAut.Outer ParrottGroup) ≤ 2 :=
  parrott_outer_card_le_two_of_restriction_range
    (sylowRestriction_range_card_le_compatible.trans hlocal)

/-- The certified compatible local count bounds every global Sylow restriction. -/
public theorem sylowRestriction_range_card_le :
    Nat.card sylowRestriction.range ≤ 2048 :=
  sylowRestriction_range_card_le_compatible.trans compatibleSylowRestrictions_card_le

/-- There are at most 4096 full automorphisms preserving the marked Sylow subgroup. -/
public theorem sylowStabilizer_card_le : Nat.card sylowStabilizer ≤ 4096 :=
  sylowStabilizer_card_le_of_range sylowRestriction_range_card_le

/-- The full outer automorphism group of the certified Atlas carrier has order at most two. -/
public theorem atlas_outer_card_le_two : Nat.card (MulAut.Outer Atlas1600Group) ≤ 2 :=
  atlas_outer_card_le_two_of_restriction_range sylowRestriction_range_card_le

/-- The full outer automorphism group of the presented Tits group has order at most two.
This discharges the sharp outer-order premise in the binary Ree derived-action argument. -/
public theorem parrott_outer_card_le_two : Nat.card (MulAut.Outer ParrottGroup) ≤ 2 :=
  parrott_outer_card_le_two_of_compatible compatibleSylowRestrictions_card_le

/-- All automorphisms of the presented Tits group have total order at most 35942400. -/
public theorem parrott_aut_card_le : Nat.card (MulAut ParrottGroup) ≤ 35942400 :=
  parrott_aut_card_le_of_restriction_range sylowRestriction_range_card_le

end Tits.SharpOuterBound
