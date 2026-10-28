module
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Mathlib.Tactic

/-!
# Fixed products for a reflected quaternion lift

For the orthogonal-transvection lift in the quaternion central product, the
outer action on the second quaternion factor supplies an element of square the
central involution. A noncentral partner in the first factor then gives a
noncentral involution fixed by the order-four lift. This is the finite
calculation used in Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

private theorem quaternion_partner (D : Type*) [Group D] (e : D≃*QuaternionGroup 2)
    (a : D) (ha : orderOf a=4) :
    ∃c:D, c^2=a^2 ∧ a*c*a⁻¹=c⁻¹ ∧ c∉center D := by
  have ha2 : (e a)^2≠1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [e.orderOf_eq,ha] at hd
    norm_num at hd
  have ht : ∀a:QuaternionGroup 2,a^2≠1 → ∃c:QuaternionGroup 2,
      c^2=a^2 ∧ a*c*a⁻¹=c⁻¹ ∧ ¬∀x:QuaternionGroup 2,x*c=c*x := by decide +kernel
  obtain ⟨c,hc2,hac,hcZ⟩ := ht (e a) ha2
  refine ⟨e.symm c,?_,?_,?_⟩
  · apply e.injective
    simpa only [map_pow,e.apply_symm_apply] using hc2
  · apply e.injective
    simpa only [map_mul,map_inv,e.apply_symm_apply] using hac
  · intro hz
    apply hcZ
    intro x
    have hh := congrArg e (mem_center_iff.mp hz (e.symm x))
    simpa only [map_mul,e.apply_symm_apply] using hh

/-- A reflected quaternion cover has a fixed noncentral product involution. -/
theorem quaternion_reflection_fixed_product
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B⊓C:Subgroup G)=2)
    (hc : ∀b∈B,∀c∈C,b*c=c*b)
    (y z a : G) (hyB : y∈centralizer (B:Set G))
    (hy2 : y^2=z) (hz : z∈B⊓C) (_hz1 : z≠1)
    (haB : a∈B) (ha4 : orderOf a=4) (ha2 : a^2=z)
    (α : MulAut C) (hα : α^2=1)
    (ho : ¬∃d:C,∀x:C,α x=d*x*d⁻¹)
    (hαy : ∀c:C,(α c:G)=y*c*y⁻¹) :
    ∃b∈C,∃c∈B,
      b^2=z ∧ c^2=z ∧ (b*c)^2=1 ∧
      b*c∉centralizer (↑(B⊔C):Set G) ∧
      (y*a)*(b*c)=(b*c)*(y*a) ∧ (y*a)^2=1 := by
  have hz2 : (⟨z,hz.2⟩:C)^2=1 := by
    have hh := pow_card_eq_one' (x:=(⟨z,hz⟩:(B⊓C:Subgroup G)))
    rw [hi] at hh
    exact Subtype.ext (congrArg (fun q:(B⊓C:Subgroup G)=>(q:G)) hh)
  have hf := (quaternion_outer_involution_fibers hC.some α hα ho).1 ⟨z,hz.2⟩ hz2
  obtain ⟨b,hb⟩ : Nonempty {b:C // b⁻¹*α b=⟨z,hz.2⟩} :=
    (Nat.card_pos_iff.mp (by rw [hf.1]; omega)).1
  have hb2 : (b:G)^2=z := congrArg Subtype.val (hf.2 b hb)
  have hby : y*(b:G)*y⁻¹=(b:G)⁻¹ := by
    rw [←hαy]
    have hh := congrArg Subtype.val hb
    change (b:G)⁻¹*(α b:G)=z at hh
    have hαb : (α b:G)=(b:G)*z := by rw [←hh]; group
    rw [hαb,←hb2]
    have hpow : (b:G)^4=1 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,hb2]; exact congrArg Subtype.val (show (⟨z,hz.2⟩:C)^2=1 from hz2)
    have hinv : (b:G)*((b:G)^2)=(b:G)⁻¹ := by
      apply mul_left_cancel (a:=(b:G))
      calc
        (b:G)*((b:G)*((b:G)^2))=(b:G)^4 := by simp only [pow_succ,pow_zero]; group
        _=1 := hpow
        _=(b:G)*(b:G)⁻¹ := (mul_inv_cancel _).symm
    exact hinv
  obtain ⟨c,hc2,hac,hcZ⟩ := quaternion_partner B hB.some ⟨a,haB⟩
    ((orderOf_injective B.subtype B.subtype_injective ⟨a,haB⟩).symm.trans ha4)
  have hc2G : (c:G)^2=z := (congrArg Subtype.val hc2).trans ha2
  have hacG : a*(c:G)*a⁻¹=(c:G)⁻¹ := congrArg Subtype.val hac
  have hbcomm : Commute (b:G) (c:G) := (hc c c.property b b.property).symm
  have hm2 : ((b:G)*(c:G))^2=1 := by
    rw [hbcomm.mul_pow,hb2,hc2G]
    simpa only [pow_two,coe_mul,coe_one] using congrArg Subtype.val (show (⟨z,hz.2⟩:C)^2=1 from hz2)
  have hnon : (b:G)*(c:G)∉centralizer (↑(B⊔C):Set G) := by
    intro hh
    apply hcZ
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx := hh (x:G) (mem_sup_left x.property)
    have hxb := hc x x.property b b.property
    apply mul_left_cancel (a:=(b:G))
    calc
      (b:G)*((x:G)*(c:G))=(x:G)*((b:G)*(c:G)) := by rw [←mul_assoc,←hxb,mul_assoc]
      _=((b:G)*(c:G))*(x:G) := hx
      _=(b:G)*((c:G)*(x:G)) := mul_assoc _ _ _
  have hyc : y*(c:G)*y⁻¹=(c:G) := by
    have hh := hyB c c.property
    rw [←hh]
    group
  have hyac : (y*a)*(c:G)*(y*a)⁻¹=(c:G)⁻¹ := by
    calc
      _=y*(a*(c:G)*a⁻¹)*y⁻¹ := by group
      _=y*(c:G)⁻¹*y⁻¹ := by rw [hacG]
      _=(c:G)⁻¹ := by rw [←conj_inv,hyc]
  have hyab : (y*a)*(b:G)*(y*a)⁻¹=(b:G)⁻¹ := by
    have hab := hc a haB b b.property
    calc
      _=y*(a*(b:G)*a⁻¹)*y⁻¹ := by group
      _=y*(b:G)*y⁻¹ := by rw [hab]; group
      _=(b:G)⁻¹ := hby
  have hfix : (y*a)*((b:G)*(c:G))=(b:G)*(c:G)*(y*a) := by
    apply mul_right_cancel (b:=(y*a)⁻¹)
    calc
      (y*a)*((b:G)*(c:G))*(y*a)⁻¹=
          ((y*a)*(b:G)*(y*a)⁻¹)*((y*a)*(c:G)*(y*a)⁻¹) := by group
      _=(b:G)⁻¹*(c:G)⁻¹ := by rw [hyab,hyac]
      _=((b:G)*(c:G))⁻¹ := by rw [hbcomm.inv_inv.eq,mul_inv_rev]
      _=(b:G)*(c:G) := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hm2)
      _=((b:G)*(c:G)*(y*a))*(y*a)⁻¹ := by group
  have hya : (y*a)^2=1 := by
    rw [(show Commute y a from (hyB a haB).symm).mul_pow,hy2,ha2]
    simpa only [pow_two,coe_mul,coe_one] using congrArg Subtype.val (show (⟨z,hz.2⟩:C)^2=1 from hz2)
  exact ⟨b,b.property,c,c.property,hb2,hc2G,hm2,hnon,hfix,hya⟩
end Subgroup
