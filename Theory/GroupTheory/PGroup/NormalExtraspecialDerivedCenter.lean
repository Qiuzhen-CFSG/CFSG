module

public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The derived-center line above a normal extraspecial subgroup

If a finite group has a normal extraspecial two-subgroup and abelian quotient,
its derived subgroup intersected with its center is exactly the embedded
extraspecial center. Indeed the ambient derived subgroup lies in the normal
subgroup, whereas that subgroup's derived group is its center of order two.
Normality makes this order-two center central in the ambient group.

The intersection is characteristic, so an ambient normalizer fixes its
nonidentity element. This is the characteristic-line step in Janko–Thompson,
Math. Z. 113 (1970), §4, Case 1, printed p.392.
-/

/-- The derived subgroup of an extraspecial two-group is its center. -/
public theorem IsExtraspecial.commutator_eq_center_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P] :
    _root_.commutator P = Subgroup.center P := by
  have hle : _root_.commutator P ≤ Subgroup.center P :=
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
  have hne : _root_.commutator P ≠ ⊥ := by
    intro h
    let : Nontrivial (P ⧸ Subgroup.center P) := IsExtraspecial.quotient_nontrivial 2 P
    exact QuotientGroup.nontrivial_iff.mp inferInstance
      ((commutator_eq_bot_iff_center_eq_top P).mp h)
  have hn : Nat.card (_root_.commutator P) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hb := Subgroup.card_le_of_le hle
  rw [IsExtraspecial.center_order_p 2 P] at hb
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [IsExtraspecial.center_order_p 2 P]
  have hp := Nat.card_pos (α := _root_.commutator P)
  omega

namespace Subgroup

/-- An abelian extension of a normal extraspecial two-group has the same
central derived line as that subgroup. -/
public theorem derived_inf_center_eq_of_normal_extraspecial
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal] [IsExtraspecial 2 D]
    [IsMulCommutative (P ⧸ D)] :
    _root_.commutator P ⊓ center P = (center D).map D.subtype := by
  have hder : _root_.commutator P ≤ D :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hZcard : Nat.card ((center D).map D.subtype) = 2 := by
    rw [card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 2 D]
  have hZcenter : (center D).map D.subtype ≤ center P :=
    central_of_normal_card_two _ hZcard
  apply le_antisymm
  · intro x hx
    refine ⟨⟨x, hder hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
    intro d
    exact Subtype.ext (mem_center_iff.mp hx.2 d)
  · apply le_inf _ hZcenter
    rw [← IsExtraspecial.commutator_eq_center_two (P := D), map_subtype_commutator]
    exact commutator_mono le_top le_top

/-- The derived-center intersection is characteristic, hence its ambient
normalizer fixes any involution generating its image. -/
public theorem normalizer_le_centralizer_of_derived_center_line
    {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (z : G) (hz : orderOf z = 2)
    (hline : (_root_.commutator C ⊓ center C).map C.subtype = zpowers z) :
    normalizer (C : Set G) ≤ centralizer ({z} : Set G) := by
  let K := _root_.commutator C ⊓ center C
  let : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f x hx
    exact ⟨characteristic_iff_le_comap.mp inferInstance f hx.1,
      characteristic_iff_le_comap.mp inferInstance f hx.2⟩
  exact normalizer_le_centralizer_of_characteristic_involution C K z hz hline

end Subgroup
