module
public import Theory.GroupTheory.PGroup.CubicCenterInvolution
public import Theory.GroupTheory.FixedInvertedFactorization
public import Theory.GroupAction.CentralInversionFixedLift
public import Theory.GroupAction.TernaryCubicFixedCard

/-!
# Cubic fixed points commuting with central inversion

In an odd group of class two, an involution fixing the center and having
abelian fixed subgroup fixes precisely the center. Factor an arbitrary
element into a fixed part and an inverted part. A fixed element commutes
with the first part; its central commutator with the second is both fixed
and inverted, hence trivial.

For an extraspecial group J of order 243, a commuting cubic automorphism
fixing the center therefore has at least 27 fixed points. On the elementary
quotient J/Z(J), cubic displacement has cube zero, giving at least nine
fixed points. Central inversion lifts those fixed cosets exactly, and the
central kernel contributes the remaining factor three.

The fixed/inverted decomposition is Gorenstein–Walter, Section 2, Lemma 4(i)
(see FixedInvertedFactorization). The source consumer is the actual paired
core join in Aschbacher–Smith I.4.5's exceptional q=3 analysis, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace MulAut
variable {J : Type*} [Group J] [Finite J]

/-- In class two, an involution fixing the center and having abelian fixed group fixes just the center. -/
theorem fixed_eq_center_of_abelian_fixed (a : MulAut J) (ha : Function.Involutive a)
    (hodd : Odd (Nat.card J)) (hclass : _root_.commutator J ≤ center J)
    (hcenter : ∀ z ∈ center J, a z=z) (hcomm : IsMulCommutative a.fixedSubgroup) :
    a.fixedSubgroup=center J := by
  let := hcomm
  apply le_antisymm
  · intro x hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨⟨u,v⟩,⟨hu,hv,he⟩,_⟩ := existsUnique_fixed_inverted_mul_of_odd_card hodd a ha y
    have hxu : Commute x u := congrArg Subtype.val
      (mul_comm' (⟨x,hx⟩:a.fixedSubgroup) ⟨u,(mem_fixedSubgroup a u).mpr hu⟩)
    have hxc := hclass (commutator_mem_commutator (mem_top x) (mem_top v))
    have hfix := hcenter ⁅x,v⁆ hxc
    rw [map_commutatorElement,(mem_fixedSubgroup a x).mp hx,hv] at hfix
    have hinv : ⁅x,v⁆⁻¹=⁅x,v⁆ := by
      have hh := (Subgroup.ClassTwo.commutatorHom hclass x).map_inv v
      exact hh.symm.trans hfix
    have hsquare : ⁅x,v⁆^2=1 := (pow_two _).trans (by simpa only [hinv] using inv_mul_cancel ⁅x,v⁆)
    have hone : ⁅x,v⁆=1 := hodd.coprime_two_right.pow_left_bijective.injective
      (hsquare.trans (one_pow 2).symm)
    have hxv : Commute x v := commutatorElement_eq_one_iff_mul_comm.mp hone
    rw [←he]
    exact (hxu.mul_right hxv).eq.symm
  · intro z hz
    exact (mem_fixedSubgroup a z).mpr (hcenter z hz)

/-- A cubic automorphism commuting with central inversion on an extraspecial
three-group of order 243 has at least 27 fixed elements. -/
theorem cubic_fixed_card_ge_twentySeven_of_central_involution
    [IsExtraspecial 3 J] (hJ : Nat.card J=243)
    (a b : MulAut J) (ha : Function.Involutive a) (hb : b^3=1)
    (hab : a*b=b*a) (haZ : ∀ z ∈ center J, a z=z)
    (hbZ : ∀ z ∈ center J, b z=z)
    (hcomm : IsMulCommutative a.fixedSubgroup) : 27≤Nat.card b.fixedSubgroup := by
  let W := center J
  let q := QuotientGroup.mk' W
  have hW : Nat.card W=3 := IsExtraspecial.center_order_p 3 J
  let : IsElementaryAbelian 3 (J ⧸ W) := IsExtraspecial.quotient_elementary_abelian 3 J
  have hclass : _root_.commutator J≤center J :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hfix : a.fixedSubgroup=W := a.fixed_eq_center_of_abelian_fixed ha
    (by rw [hJ]; decide) hclass haZ hcomm
  have hoddW : Odd (Nat.card W) := by rw [hW]; decide
  have hinv := (a.quotient_inversion_of_odd_fixed_kernel ha W hoddW
    (fun x => (mem_fixedSubgroup a x).symm.trans (by rw [hfix]))).1
  have hmap : W.map b.toMonoidHom=W := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩; change b w∈W; rwa [hbZ w hw]
    · intro hx; exact ⟨x,hx,hbZ x hx⟩
  let β : MulAut (J ⧸ W) := QuotientGroup.congr W W b hmap
  have hβ (x : J) : β (q x)=q (b x) := rfl
  have hβ3 : β^3=1 := by
    ext u
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective W u
    change β (β (β (q x)))=q x
    rw [hβ,hβ,hβ,show b (b (b x))=x from DFunLike.congr_fun hb x]
  have hlift (x : J) (hx : β (q x)=q x) : b x=x := by
    apply fixed_of_central_displacement_of_inverted_quotient a b hab W le_rfl hoddW
      haZ hbZ hinv x
    apply (QuotientGroup.eq_one_iff _).mp
    change q (b x*x⁻¹)=1
    rw [map_mul,map_inv,←hβ,hx,mul_inv_cancel]
  let f : b.fixedSubgroup →* β.fixedSubgroup := {
    toFun x := ⟨q x,by
      rw [mem_fixedSubgroup,hβ,(mem_fixedSubgroup b x).mp x.property]⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' x y := Subtype.ext (map_mul q (x:J) (y:J)) }
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective W (u:J ⧸ W)
    refine ⟨⟨x,(mem_fixedSubgroup b x).mpr (hlift x ?_)⟩,Subtype.ext hx⟩
    rw [hx]; exact (mem_fixedSubgroup β u).mp u.property
  let e : f.ker ≃ W := {
    toFun x := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.property)⟩
    invFun w := ⟨⟨w,(mem_fixedSubgroup b w).mpr (hbZ w w.property)⟩,
      Subtype.ext ((QuotientGroup.eq_one_iff _).mpr w.property)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card b.fixedSubgroup=3*Nat.card β.fixedSubgroup := by
    have hh := f.ker.card_mul_index
    rw [Nat.card_congr e,hW,index_ker,MonoidHom.range_eq_top.mpr hf,card_top] at hh
    exact hh.symm
  have hQ : Nat.card (J ⧸ W)=81 := by
    have hh := W.card_mul_index
    rw [hW,hJ,index] at hh
    omega
  have hbound := β.ternary_cubic_fixed_card_bound hβ3
  rw [hQ] at hbound
  have hdiv : Nat.card β.fixedSubgroup ∣ 81 := hQ ▸ β.fixedSubgroup.card_subgroup_dvd_card
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=4)).mp hdiv
  rw [hc,he]
  rw [he] at hbound
  interval_cases i
  all_goals norm_num at hbound
  all_goals norm_num

end MulAut
