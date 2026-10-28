module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondCenter
public import Theory.SpecificGroups.Tits.RelativeSylowMarking
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Sylow stabilizers and the two Tits parabolic normalizers

Every automorphism preserving the certified Sylow subgroup fixes r5,
its unique nonidentity central element. Thus identifying the first
parabolic with C(r5) proves its invariance. For the second parabolic,
a characteristic Sylow subgroup with that parabolic as full normalizer
gives the same conclusion by transport of characteristic subgroups.

The centralizer identification, the characteristic property of the
explicit secondCenter subgroup, and its normalizer identification remain
explicit premises here. The imported normal two-subgroup calculation
already proves r5 belongs to the second parabolic's actual two-core.

Source: Aschbacher–Smith 2.3.9(7), printed p.526; Parrott (1972), pp.672,683.
-/

@[expose] public section
open Subgroup
namespace Tits.RelativeParabolicNormalizers

/-- Sylow preservation fixes its unique nonidentity central element. -/
theorem fixes_r5 (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    β atlas1600R5 = atlas1600R5 := by
  apply RelativeSylowMarking.image_eq_r5_of_sylow_center β atlas1600SylowTwo
  · simpa only [atlas1600SylowTwo_coe] using hβ
  · simpa only [atlas1600SylowTwo_coe] using atlas1600R5_mem_sylowTwo
  · intro s hs
    exact congrArg Subtype.val
      (mem_center_iff.mp atlas1600R5_mem_center_sylowTwo ⟨s, by
        change s ∈ (atlas1600SylowTwo : Subgroup Atlas1600Group) at hs
        rwa [atlas1600SylowTwo_coe] at hs⟩)
  · exact atlas1600R5_ne_one

/-- The first stabilizer calculation reduces to its full centralizer identity. -/
theorem first_stabilized_of_centralizer
    (hfirst : ExceptionalParabolics.first = centralizer {atlas1600R5})
    (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    ExceptionalParabolics.first.map β.toMonoidHom = ExceptionalParabolics.first := by
  apply eq_of_le_of_card_ge
  · rw [hfirst]
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, fixes_r5 β hβ] using
      map_centralizer_le_centralizer_image {atlas1600R5} β.toMonoidHom
  · rw [card_map_of_injective β.injective]

private theorem image_characteristic (R : Subgroup Atlas1600Group) (Q : Subgroup R) [Q.Characteristic]
    (β : MulAut Atlas1600Group) (hβ : R.map β.toMonoidHom = R) :
    (Q.map R.subtype).map β.toMonoidHom = Q.map R.subtype := by
  let α : MulAut R := (β.subgroupMap R).trans (MulEquiv.subgroupCongr hβ)
  have he : β.toMonoidHom.comp R.subtype = R.subtype.comp α.toMonoidHom := rfl
  rw [Subgroup.map_map, he, ← Subgroup.map_map,
    (characteristic_iff_map_eq.mp (inferInstance : Q.Characteristic)) α]
/-- The second stabilizer calculation reduces to a characteristic-normalizer identity. -/
theorem second_stabilized_of_characteristic_normalizer
    (hchar : (secondCenter.subgroupOf atlas1600SylowTwoSubgroup).Characteristic)
    (hsecond : ExceptionalParabolics.second = normalizer (secondCenter : Set Atlas1600Group))
    (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    ExceptionalParabolics.second.map β.toMonoidHom = ExceptionalParabolics.second := by
  let := hchar
  have he := image_characteristic atlas1600SylowTwoSubgroup
    (secondCenter.subgroupOf atlas1600SylowTwoSubgroup) β hβ
  rw [map_subgroupOf_eq_of_le secondCenter_le_sylow] at he
  rw [hsecond, map_equiv_normalizer_eq, he]

end Tits.RelativeParabolicNormalizers

end
