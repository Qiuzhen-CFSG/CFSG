module

public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Quaternion involution fusion with a two-group centralizer

An order-nine subgroup fuses the noncentral involutions of a normal central
product of two quaternion eights when the ambient centralizer is a two-group.
The centralizer may extend beyond the quaternion product.

Restrict to the join of the quaternion product and the given order-nine
subgroup. Modulo the product, the images of its centralizer and the join
are respectively a two-group and a three-group, so their intersection is
trivial. The product is therefore self-centralizing in the join, where the
existing involution-orbit theorem applies. The original factors and
involutions are retained through the canonical subgroup equivalence.

Source: Aschbacher--Smith, Proposition 13.5.16, printed p.921, the involution
fusion in the S₆ extension case; the quaternion action calculation is the
one already proved in `QuaternionCentralProductNineOrbit`.
-/

namespace Subgroup

private theorem centralizer_in_join_le
    {G : Type*} [Group G] (U : Subgroup G) [U.Normal]
    (hcent : IsPGroup 2 (centralizer (U : Set G)))
    (A : Subgroup G) (hA : IsPGroup 3 A) :
    centralizer (U.subgroupOf (U ⊔ A) : Set (U ⊔ A : Subgroup G)) ≤
      U.subgroupOf (U ⊔ A) := by
  let q := QuotientGroup.mk' U
  have himage : (U ⊔ A).map q = A.map q := by
    rw [map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hdis := IsPGroup.disjoint_of_coprime (hcent.map q) (hA.map q)
    (by decide : Nat.Coprime 2 3)
  intro x hx
  have hxc : (x : G) ∈ centralizer (U : Set G) := by
    intro u hu
    exact congrArg Subtype.val (hx (⟨u, mem_sup_left hu⟩ : (U ⊔ A : Subgroup G)) hu)
  have hxA : q (x : G) ∈ A.map q :=
    himage ▸ mem_map_of_mem q x.property
  exact (QuotientGroup.eq_one_iff (x : G)).mp
    (disjoint_def.mp hdis (mem_map_of_mem q hxc) hxA)

/-- An order-nine subgroup fuses noncentral involutions in a normal quaternion
central product whose ambient centralizer is a two-group. -/
public theorem isConj_noncentral_involutions_of_order_nine_of_two_centralizer
    {G : Type*} [Group G] [Finite G] (U : Subgroup G) [U.Normal]
    (hcent : IsPGroup 2 (centralizer (U : Set G)))
    (d : QuaternionCentralProductData U) (A : Subgroup G) (hA : Nat.card A = 9)
    (x y : U) (hx : orderOf x = 2) (hxZ : x ∉ center U)
    (hy : orderOf y = 2) (hyZ : y ∉ center U) : IsConj (x : G) (y : G) := by
  let K := U ⊔ A
  let UK := U.subgroupOf K
  let AK := A.subgroupOf K
  let e : UK ≃* U := subgroupOfEquivOfLe le_sup_left
  let dK := d.map e.symm
  have hself : centralizer (UK : Set K) ≤ UK :=
    centralizer_in_join_le U hcent A (IsPGroup.of_card (n := 2) hA)
  have hAK : Nat.card AK = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ K from le_sup_right)).toEquiv).trans hA
  have hn (z : U) (hz : z ∉ center U) : e.symm z ∉ center UK := by
    intro hc
    apply hz
    have hh : e (e.symm z) ∈ center U := (centerCongr e ⟨e.symm z, hc⟩).property
    rwa [e.apply_symm_apply] at hh
  have hconj := isConj_noncentral_involutions_of_order_nine UK hself
    dK.left dK.right dK.left_model dK.right_model dK.span dK.intersection_card dK.commute
    AK hAK (e.symm x) (e.symm y) ((e.symm.orderOf_eq x).trans hx) (hn x hxZ)
      ((e.symm.orderOf_eq y).trans hy) (hn y hyZ)
  exact K.subtype.map_isConj hconj
end Subgroup
