module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The two quaternion factors and their relative normality

The two factors of a quaternion–quaternion central product are exactly its
quaternion subgroups. Every automorphism permutes this pair, so it preserves
one factor precisely when it preserves the other. For a normal embedding
into an overgroup, the two embedded factors therefore have the same normality
status in that overgroup.

The proof uses the intrinsic quaternion-subgroup classification, injectivity
of automorphism transport, and the literal conjugation action of the overgroup.
Source application: Aschbacher–Smith, I.4.6, printed p.417.
-/

namespace Subgroup.QuaternionCentralProductData

variable {P : Type*} [Group P] [Finite P] (d : QuaternionCentralProductData P)

omit [Finite P] in
public theorem factors_ne : d.left ≠ d.right := by
  intro he
  have hc : Nat.card d.left = 8 := by
    rw [Nat.card_congr d.left_model.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hi := d.intersection_card
  rw [← he, inf_idem, hc] at hi
  omega

public theorem quaternion_subgroup_iff (R : Subgroup P) :
    Nonempty (R ≃* QuaternionGroup 2) ↔ R = d.left ∨ R = d.right := by
  constructor
  · intro hR
    exact quaternion_subgroup_eq_factor d.left d.right R d.left_model d.right_model
      d.intersection_card d.commute hR (by rw [d.span]; exact le_top)
  · rintro (rfl | rfl)
    · exact d.left_model
    · exact d.right_model

include d in
public theorem quaternion_subgroups_card :
    Nat.card {R : Subgroup P // Nonempty (R ≃* QuaternionGroup 2)} = 2 := by
  have he : {R : Subgroup P | Nonempty (R ≃* QuaternionGroup 2)} = {d.left, d.right} := by
    ext R
    exact d.quaternion_subgroup_iff R
  rw [show Nat.card {R : Subgroup P // Nonempty (R ≃* QuaternionGroup 2)} =
    Nat.card ({R : Subgroup P | Nonempty (R ≃* QuaternionGroup 2)} : Set (Subgroup P)) from rfl,
    he, Nat.card_coe_set_eq, Set.ncard_pair d.factors_ne]

public theorem map_left_eq_iff_map_right_eq (a : MulAut P) :
    d.left.map a.toMonoidHom = d.left ↔ d.right.map a.toMonoidHom = d.right := by
  have himage (R : Subgroup P) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
      R.map a.toMonoidHom = d.left ∨ R.map a.toMonoidHom = d.right :=
    (d.quaternion_subgroup_iff _).mp ⟨(a.subgroupMap R).symm.trans hR.some⟩
  constructor
  · intro hl
    rcases himage d.right d.right_model with hr | hr
    · exact (d.factors_ne (map_injective a.injective (hl.trans hr.symm))).elim
    · exact hr
  · intro hr
    rcases himage d.left d.left_model with hl | hl
    · exact hl
    · exact (d.factors_ne (map_injective a.injective (hl.trans hr.symm))).elim

public theorem normal_left_iff_normal_right
    {H : Type*} [Group H] (Q : Subgroup H) [Q.Normal] [Finite Q]
    (d : QuaternionCentralProductData Q) :
    (d.left.map Q.subtype).Normal ↔ (d.right.map Q.subtype).Normal := by
  have hm (R : Subgroup Q) (g : H) :
      (R.map (MulAut.conjNormal g).toMonoidHom).map Q.subtype =
        (R.map Q.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  have hn (R : Subgroup Q) : (R.map Q.subtype).Normal ↔
      ∀ g : H, R.map (MulAut.conjNormal g).toMonoidHom = R := by
    rw [normal_iff_map_conj_eq]
    constructor
    · intro h g
      apply map_injective Q.subtype_injective
      rw [hm]
      exact h g
    · intro h g
      change (R.map Q.subtype).map (MulAut.conj g).toMonoidHom = R.map Q.subtype
      rw [← hm, h g]
  rw [hn, hn]
  exact forall_congr' fun g => d.map_left_eq_iff_map_right_eq (MulAut.conjNormal g)

end Subgroup.QuaternionCentralProductData
