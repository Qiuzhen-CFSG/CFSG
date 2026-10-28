module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.Unitriangular
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionTypes

/-!
# Involution selection inside the split binary Sylow group

Every involution outside the index-two quaternion core belongs to the
middle sixteen and generates that sixteen with its commutator with the
core. This uses the actual six-coordinate multiplication, and therefore
does not assume that an arbitrary outside element has order two.

The middle eight in U is elementary and centralized by each such
involution. The explicit self-centralizer calculation in the entire
Sylow group forces interchange of the two quaternion factors. Hence
its action on the literal central square quotient is a2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. Choosing an involution in the source W^g remains
an additional obligation. The core's embedded quaternion data are a
source hypothesis, and are not inferred merely from its order.
-/

@[expose] public section
set_option synthInstance.maxSize 512

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
open Subgroup
open scoped IsMulCommutative commutatorElement

instance : U.Normal := U.normal_of_index_eq_two (by
 have h := U.card_mul_index
 rw [card_U, card_T] at h
 omega)

theorem selfcentralizing_U : centralizer (U : Set T) ≤ U := by
 intro x hx
 have hr := hx r (show r ∈ U from rfl)
 have hq := hx q (show q ∈ U from rfl)
 exact (by decide +kernel : ∀ x : T, r*x=x*r → q*x=x*q → x ∈ U) x hr hq

theorem fixed_eight_card : Nat.card (U ⊓ A : Subgroup T) = 8 := by
 let : DecidablePred (· ∈ (U ⊓ A : Subgroup T)) := fun x =>
  inferInstanceAs (Decidable (x.x23=0 ∧ x.x12=0 ∧ x.x34=0))
 rw [Nat.card_eq_fintype_card]
 decide +kernel

theorem a2_of_mem_A_outside (d : QuaternionCentralProductData U)
    (x : T) (hxA : x ∈ A) (hxU : x ∉ U) :
 d.IsA2Action (U.normalizerMonoidHom ⟨x, by rw [U.normalizer_eq_top]; trivial⟩) := by
 let B := d.left.map U.subtype
 let C := d.right.map U.subtype
 have hj : B ⊔ C = U := by
  rw [← Subgroup.map_sup, d.span, ← MonoidHom.range_eq_map, U.range_subtype]
 have hB : Nonempty (B ≃* QuaternionGroup 2) :=
  ⟨(d.left.equivMapOfInjective U.subtype U.subtype_injective).symm.trans d.left_model.some⟩
 have hC : Nonempty (C ≃* QuaternionGroup 2) :=
  ⟨(d.right.equivMapOfInjective U.subtype U.subtype_injective).symm.trans d.right_model.some⟩
 have hi : Nat.card (B ⊓ C : Subgroup T) = 2 := by
  rw [← map_inf d.left d.right U.subtype U.subtype_injective,
    card_map_of_injective U.subtype_injective, d.intersection_card]
 have hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
  rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
  exact congrArg U.subtype (d.commute b hb c hc)
 have hn : x ∈ normalizer (U : Set T) := by rw [U.normalizer_eq_top]; trivial
 have hswap := (quaternion_factors_swapped_of_fixed_elementary_eight B C (U ⊓ A)
  hB hC hi hc (by rw [hj]; exact card_U) (by rw [hj]; exact selfcentralizing_U)
  (by rw [hj]; exact inf_le_left) fixed_eight_card
  (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu.2)
  x (hj.symm ▸ hn) (hj.symm ▸ hxU)
  (fun u hu => (by
    exact (show Commute (⟨x,hxA⟩ : A) ⟨u,hu.2⟩ from Commute.all _ _).map A.subtype))).1
 let α := U.normalizerMonoidHom ⟨x,hn⟩
 have ha : α^2=1 := by
  have h : (⟨x,hn⟩ : normalizer (U : Set T))^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hxA)
  dsimp [α]
  rw [← map_pow,h,map_one]
 apply d.isA2Action_of_swap α ha
 apply Subgroup.map_injective U.subtype_injective
 rw [Subgroup.map_map]
 change d.left.map ((MulAut.conj x).toMonoidHom.comp U.subtype) = _
 rw [← Subgroup.map_map]
 exact hswap
theorem outside_involution_mem_middle : ∀ x : T, x ∉ U → x^2=1 → x ∈ A := by
 decide +kernel

theorem generation_of_mem_A_outside (x : T) (hxA : x ∈ A) (hxU : x ∉ U) :
 zpowers x ⊔ ⁅U,zpowers x⁆ = A := by
 let D := ⁅U,zpowers x⁆
 let B := zpowers x ⊔ D
 have hr : r ∈ U := rfl
 have hq : q ∈ U := rfl
 have hx : x ∈ zpowers x := mem_zpowers x
 have hz : bit 1 ∈ D := by
  have he : ⁅r*q,x⁆ * ⁅r,x⁆ * ⁅q,x⁆ = bit 1 :=
   (by decide +kernel : ∀ x : T, x ∈ A → x ∉ U →
    ⁅r*q,x⁆ * ⁅r,x⁆ * ⁅q,x⁆ = bit 1) x hxA hxU
  rw [← he]
  exact mul_mem (mul_mem (commutator_mem_commutator (U.mul_mem hr hq) hx)
    (commutator_mem_commutator hr hx)) (commutator_mem_commutator hq hx)
 have hb : bit 0 ∈ D := by
  have he : ⁅r,x⁆ * bit 1 ^ x.x24.val = bit 0 :=
   (by decide +kernel : ∀ x : T, x ∈ A → x ∉ U →
    ⁅r,x⁆ * bit 1 ^ x.x24.val = bit 0) x hxA hxU
  rw [← he]
  exact mul_mem (commutator_mem_commutator hr hx) (pow_mem hz _)
 have he : bit 3 ∈ D := by
  have he : ⁅q,x⁆ * bit 1 ^ x.x13.val = bit 3 :=
   (by decide +kernel : ∀ x : T, x ∈ A → x ∉ U →
    ⁅q,x⁆ * bit 1 ^ x.x13.val = bit 3) x hxA hxU
  rw [← he]
  exact mul_mem (commutator_mem_commutator hq hx) (pow_mem hz _)
 have hbit0 : bit 0 ∈ B := (show D ≤ B from le_sup_right) hb
 have hbit1 : bit 1 ∈ B := (show D ≤ B from le_sup_right) hz
 have hbit3 : bit 3 ∈ B := (show D ≤ B from le_sup_right) he
 have hbit2 : bit 2 ∈ B := by
  have ht : x * bit 0 ^ x.x13.val * bit 1 ^ x.x14.val * bit 3 ^ x.x24.val = bit 2 :=
   (by decide +kernel : ∀ x : T, x ∈ A → x ∉ U →
    x * bit 0 ^ x.x13.val * bit 1 ^ x.x14.val * bit 3 ^ x.x24.val = bit 2) x hxA hxU
  rw [← ht]
  exact mul_mem (mul_mem (mul_mem
    ((show zpowers x ≤ B from le_sup_left) hx) (pow_mem hbit0 _))
      (pow_mem hbit1 _)) (pow_mem hbit3 _)
 apply le_antisymm
 · exact sup_le (zpowers_le.mpr hxA)
    ((commutator_mono (le_refl U) (zpowers_le.mpr hxA)).trans (commutator_le_right U A))
 · rw [A_eq_closure_bits]
   apply (closure_le _).mpr
   rintro y ⟨i,rfl⟩
   fin_cases i
   · exact hbit0
   · exact hbit1
   · exact hbit2
   · exact hbit3

theorem selected_a2 (d : QuaternionCentralProductData U) :
 d.IsA2Action (U.normalizerMonoidHom ⟨a, by rw [U.normalizer_eq_top]; trivial⟩) :=
 a2_of_mem_A_outside d a (by decide) a_selected.2.1
end Matrix.PSL3Two.SplitParabolic.Unitriangular
