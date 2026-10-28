module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# PSL₂(16) extended by the involutory field automorphism

The normal factor is the genuine matrix quotient over GF(16). Its specified
outer involution acts entrywise by fourth powers. The cyclic field subgroup
has order two, so the resulting semidirect product has order 8160 and its
linear factor has order 4080.

This fixes the split-extension convention needed for the subgroup mentioned
in Aschbacher–Smith I.4.7(2), printed p.418. It is an intrinsic construction;
no embedding in an arbitrary group with a specified involution centralizer
is asserted.
-/

namespace Theory.PSL2.BinaryFourFieldExtension

public theorem field_card : Nat.card (BinaryField 4) = 16 :=
  GaloisField.card 2 4 (by decide)

public theorem linear_card : Nat.card (BinaryGroup 4) = 4080 := by
  rw [← Nat.card_congr (sl2QuotientEquiv (BinaryField 4)).toEquiv,
    Atlas.card_sl_two, field_card]
  norm_num

/-- Fourth-power Frobenius on the actual field GF(16). -/
@[expose] public noncomputable def fieldInvolution : BinaryField 4 ≃+* BinaryField 4 :=
  iterateFrobeniusEquiv (BinaryField 4) 2 2

public theorem fieldInvolution_apply (a : BinaryField 4) : fieldInvolution a = a ^ 4 :=
  iterateFrobeniusEquiv_def _ 2 2 a

public theorem fieldInvolution_square : fieldInvolution ^ 2 = 1 := by
  let : Fintype (BinaryField 4) := Fintype.ofFinite _
  ext a
  change (a ^ 4) ^ 4 = a
  rw [← pow_mul]
  have hc : Fintype.card (BinaryField 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, field_card]
  simpa only [hc] using FiniteField.pow_card a

public theorem fieldInvolution_ne_one : fieldInvolution ≠ 1 := by
  let : Fintype (BinaryField 4) := Fintype.ofFinite _
  intro h
  have hp : ∀ a : (BinaryField 4)ˣ, a ^ 3 = 1 := by
    intro a
    apply Units.ext
    have ha := DFunLike.congr_fun h (a : BinaryField 4)
    change (a : BinaryField 4) ^ 4 = (a : BinaryField 4) at ha
    have ht : (a : BinaryField 4) ^ 3 * (a : BinaryField 4) = 1 * (a : BinaryField 4) := by
      simpa only [← pow_succ, one_mul] using ha
    exact mul_right_cancel₀ (Units.ne_zero a) ht
  have hd := (FiniteField.forall_pow_eq_one_iff (K := BinaryField 4) 3).mp hp
  have hc : Fintype.card (BinaryField 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, field_card]
  norm_num [hc] at hd

public theorem fieldInvolution_order : orderOf fieldInvolution = 2 :=
  orderOf_eq_prime fieldInvolution_square fieldInvolution_ne_one

public theorem field_action_order : orderOf (fieldAut fieldInvolution) = 2 :=
  (orderOf_fieldAut fieldInvolution).trans fieldInvolution_order

public theorem field_action_not_inner : fieldAut fieldInvolution ∉ inner (BinaryField 4) := by
  intro h
  obtain ⟨g, hg⟩ := (mem_inner_iff _ _).mp h
  exact fieldInvolution_ne_one (fieldAut_eq_conj_implies_refl fieldInvolution g hg)

/-- The order-two subgroup of field automorphisms, with its actual action. -/
public noncomputable abbrev Actor := Subgroup.zpowers fieldInvolution

@[expose] public noncomputable def action : Actor →* MulAut (BinaryGroup 4) :=
  fieldAutHom.comp Actor.subtype

/-- The split extension by fourth-power Frobenius, not the full field group. -/
public abbrev Model := BinaryGroup 4 ⋊[action] Actor

@[expose] public noncomputable def linearInclusion : BinaryGroup 4 →* Model := SemidirectProduct.inl

@[expose] public noncomputable def involution : Model :=
  SemidirectProduct.inr ⟨fieldInvolution, Subgroup.mem_zpowers _⟩

public theorem involution_order : orderOf involution = 2 := by
  rw [involution, orderOf_injective SemidirectProduct.inr
    SemidirectProduct.inr_injective, Subgroup.orderOf_mk, fieldInvolution_order]

public theorem involution_not_mem_linear : involution ∉ linearInclusion.range := by
  rintro ⟨x, hx⟩
  have he := congrArg (fun y : Model => (y.right : BinaryField 4 ≃+* BinaryField 4)) hx
  exact fieldInvolution_ne_one he.symm

public theorem conjugation (x : BinaryGroup 4) :
    involution * linearInclusion x * involution⁻¹ =
      linearInclusion (fieldAut fieldInvolution x) := by
  let a : Actor := ⟨fieldInvolution, Subgroup.mem_zpowers _⟩
  have hi : involution⁻¹ = (SemidirectProduct.inr a⁻¹ : Model) :=
    (map_inv SemidirectProduct.inr a).symm
  rw [hi]
  exact (SemidirectProduct.inl_aut (φ := action) a x).symm

public theorem generated : linearInclusion.range ⊔ Subgroup.zpowers involution = ⊤ := by
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · exact (show linearInclusion.range ≤
      linearInclusion.range ⊔ Subgroup.zpowers involution from le_sup_left) ⟨x.left, rfl⟩
  · apply (show Subgroup.zpowers involution ≤
      linearInclusion.range ⊔ Subgroup.zpowers involution from le_sup_right)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.right.property
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨k, ?_⟩
    change (SemidirectProduct.inr
      (⟨fieldInvolution, Subgroup.mem_zpowers _⟩ : Actor)) ^ k = _
    rw [← map_zpow]
    apply congrArg SemidirectProduct.inr
    exact Subtype.ext hk

public theorem model_card : Nat.card Model = 8160 := by
  rw [SemidirectProduct.card, linear_card, Nat.card_zpowers, fieldInvolution_order]

end Theory.PSL2.BinaryFourFieldExtension
