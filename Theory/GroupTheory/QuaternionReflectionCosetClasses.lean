module
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.SpecificGroups.SL2.BinaryTetrahedralOrderFour
public import Mathlib.Tactic

/-!
# Central-square classes in a reflected quaternion coset

Let Q be a central product of two actual quaternion subgroups. An actor y
centralizes an SL2(3) subgroup over the first factor and induces an outer
involution on the second. The outer quaternion norm calculation removes
the second coordinate by conjugation. The six order-four elements of the
first factor fuse in the actual SL2(3) subgroup; the two central choices
fuse by the outer quaternion difference fiber. Hence the central-square
coset has exactly the possible classes y and a y.

Source: Aschbacher--Smith 2.4.29, printed p.546. No splitting of the ambient
extension is assumed.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Remove the reflected quaternion coordinate from an element with central square. -/
theorem reflected_quaternion_coset_reduction
    (B C : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hc : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (y : G) (hyB : y ∈ centralizer (B : Set G))
    (hy2 : y^2 ∈ B ⊓ C)
    (α : MulAut C) (hα : α^2=1)
    (hαout : ¬ ∃ d : C, ∀ x : C, α x=d*x*d⁻¹)
    (hαy : ∀ c : C, (α c : G)=y*c*y⁻¹)
    (r : G) (hr : r ∈ (↑(B ⊔ C) : Set G) * ({y} : Set G))
    (hr2 : r^2 ∈ B ⊓ C) :
    ∃ b : B, ∃ d : C, (d:G)⁻¹*r*d=(b:G)*y := by
  have hn : C ≤ normalizer (B : Set G) :=
    (show C≤centralizer (B:Set G) from fun c hc' b hb=>hc b hb c hc').trans
      (centralizer_le_normalizer _)
  obtain ⟨q,hq,w,hw,hrw⟩ := hr
  have hw' : w = y := Set.mem_singleton_iff.mp hw
  subst w
  subst r
  have hq' : q ∈ (B:Set G)*(C:Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left B C hn]
  obtain ⟨b,hb,c,hc',rfl⟩ := hq'
  have hb2 : b^2∈B⊓C := by
    rw [intersection_eq_factor_center B C hB hi hc]
    obtain ⟨e⟩ := hB
    refine ⟨(⟨b,hb⟩:B)^2,mem_center_iff.mpr ?_,rfl⟩
    intro x
    apply e.injective
    simp only [map_mul,map_pow]
    exact (by decide : ∀a x : QuaternionGroup 2, x*a^2=a^2*x) _ _
  have hyb : y*b=b*y := (hyB b hb).symm
  have hαc : y*c=(α ⟨c,hc'⟩:G)*y := by
    rw [hαy]
    group
  have hbc : b*c=c*b := hc b hb c hc'
  have hbα : b*(α ⟨c,hc'⟩:G)=(α ⟨c,hc'⟩:G)*b := hc b hb _ (α ⟨c,hc'⟩).property
  have hsq : (b*c*y)^2=b^2*(c*(α ⟨c,hc'⟩:G))*y^2 := by
    simp only [pow_two]
    calc
      b*c*y*(b*c*y)=b*c*(y*b)*c*y := by group
      _=b*c*(b*y)*c*y := by rw [hyb]
      _=b*(c*b)*(y*c)*y := by group
      _=b*(b*c)*((α ⟨c,hc'⟩:G)*y)*y := by rw [←hbc,hαc]
      _=b*b*(c*(α ⟨c,hc'⟩:G))*(y*y) := by group
  have hnorm : c*(α ⟨c,hc'⟩:G)∈B⊓C := by
    have hh := (B⊓C).mul_mem ((B⊓C).mul_mem ((B⊓C).inv_mem hb2) hr2)
      ((B⊓C).inv_mem hy2)
    rw [hsq] at hh
    have he : (b^2)⁻¹*(b^2*(c*(α ⟨c,hc'⟩:G))*y^2)*(y^2)⁻¹ = c*(α ⟨c,hc'⟩:G) := by group
    rwa [he] at hh
  have hs : (⟨c,hc'⟩ * α ⟨c,hc'⟩)^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨c*(α ⟨c,hc'⟩:G),hnorm⟩:(B⊓C : Subgroup G)))
    rw [hi] at hh
    exact Subtype.ext (congrArg (fun q:(B⊓C:Subgroup G)=>(q:G)) hh)
  obtain ⟨d,hd⟩ := (quaternion_outer_involution_fibers hC.some α hα hαout).2 ⟨c,hc'⟩ hs
  have hdG : c=(d:G)*(α d:G)⁻¹ := by simpa only [coe_mul,coe_inv,map_inv] using congrArg Subtype.val hd
  refine ⟨⟨b,hb⟩,d,?_⟩
  have hyD : y*(d:G)=(α d:G)*y := by rw [hαy]; group
  have hbd : b*(d:G)=(d:G)*b := hc b hb d d.property
  rw [hdG]
  calc
    (d:G)⁻¹*(b*((d:G)*(α d:G)⁻¹)*y)*d
        =(d:G)⁻¹*b*(d:G)*(α d:G)⁻¹*(y*d) := by group
    _=(d:G)⁻¹*b*(d:G)*(α d:G)⁻¹*((α d:G)*y) := by rw [hyD]
    _=(d:G)⁻¹*b*(d:G)*y := by group
    _=(d:G)⁻¹*(d:G)*b*y := by rw [mul_assoc (d:G)⁻¹ b (d:G),hbd]; group
    _=b*y := by group

end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem quaternion_square_one_central {D : Type*} [Group D]
    (e : D ≃* QuaternionGroup 2) (a : D) (ha : a^2=1) : a ∈ center D := by
  apply mem_center_iff.mpr
  intro b
  apply e.injective
  simp only [map_mul]
  have h : ∀a : QuaternionGroup 2, a^2=1 → ∀b, b*a=a*b := by decide +kernel
  exact h (e a) (by rw [←map_pow,ha,map_one]) (e b)

/-- An odd reflection on one quaternion factor leaves only two central-square
classes in the other factor's coset. -/
theorem quaternion_reflection_coset_classes
    (B C L : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hi : Nat.card (B ⊓ C : Subgroup G)=2)
    (hc : ∀ b∈B, ∀c∈C, b*c=c*b)
    (hBL : B≤L) (eL : L ≃* GLS3.Chapter5.SchurPresentation.SL23)
    (y : G) (hyL : y∈centralizer (L:Set G)) (hy2 : y^2∈B⊓C)
    (α : MulAut C) (hα : α^2=1)
    (ho : ¬∃d:C,∀x:C,α x=d*x*d⁻¹)
    (hαy : ∀c:C,(α c:G)=y*c*y⁻¹)
    (z : G) (hz : z∈B⊓C) (hz1 : z≠1)
    (a : G) (haB : a∈B) (ha4 : orderOf a=4)
    (r : G) (hr : r∈(↑(B⊔C):Set G)*({y}:Set G)) (hr2 : r^2∈B⊓C) :
    IsConj r y ∨ IsConj r (a*y) := by
  have hyB : y∈centralizer (B:Set G) := centralizer_le hBL hyL
  obtain ⟨b,d,hd⟩ := reflected_quaternion_coset_reduction B C hB hC hi hc y hyB hy2 α hα ho hαy r hr hr2
  have hred : IsConj r ((b:G)*y) := isConj_iff.mpr ⟨(d:G)⁻¹,by simpa using hd⟩
  by_cases hb2 : b^2=1
  · have hbI : (b:G)∈B⊓C := by
      rw [intersection_eq_factor_center B C hB hi hc]
      exact ⟨b,quaternion_square_one_central hB.some b hb2,rfl⟩
    have hb : (b:G)=1 ∨ (b:G)=z := by
      obtain ⟨w,hw,huniq⟩ := (Nat.card_eq_two_iff' (1:(B⊓C:Subgroup G))).mp hi
      by_cases hb1 : (b:G)=1
      · exact Or.inl hb1
      · right
        have hh := (huniq ⟨b,hbI⟩ (fun hh=>hb1 (congrArg Subtype.val hh))).trans
          (huniq ⟨z,hz⟩ (fun hh=>hz1 (congrArg Subtype.val hh))).symm
        exact congrArg Subtype.val hh
    rcases hb with hb | hb
    · exact Or.inl (by simpa only [hb,one_mul] using hred)
    · have hz2 : (⟨z,hz.2⟩:C)^2=1 := by
        have hh := pow_card_eq_one' (x:=(⟨z,hz⟩:(B⊓C:Subgroup G)))
        rw [hi] at hh
        exact Subtype.ext (congrArg (fun q:(B⊓C:Subgroup G)=>(q:G)) hh)
      have hcard := (quaternion_outer_involution_fibers hC.some α hα ho).1 ⟨z,hz.2⟩ hz2 |>.1
      obtain ⟨x,hx⟩ : Nonempty {x:C // x⁻¹*α x=⟨z,hz.2⟩} :=
        (Nat.card_pos_iff.mp (by rw [hcard]; omega)).1
      have hxG : (x:G)⁻¹*(α x:G)=z := congrArg Subtype.val hx
      have hxy : y*(x:G)=(α x:G)*y := by rw [hαy]; group
      have hzy : IsConj y (z*y) := isConj_iff.mpr ⟨(x:G)⁻¹,by
        calc
          (x:G)⁻¹*y*((x:G)⁻¹)⁻¹=(x:G)⁻¹*(y*x) := by group
          _=(x:G)⁻¹*((α x:G)*y) := by rw [hxy]
          _=z*y := by rw [←mul_assoc,hxG]⟩
      have hred' : IsConj r (z*y) := by simpa only [hb] using hred
      exact Or.inl (hred'.trans hzy.symm)
  · have hb4 : orderOf (b:G)=4 := by
      have htable : ∀b : QuaternionGroup 2, b^4=1 := by decide +kernel
      have hbq : (hB.some b)^2≠1 := by
        intro hh
        apply hb2
        apply hB.some.injective
        simpa only [map_pow,map_one] using hh
      exact (orderOf_injective B.subtype B.subtype_injective b).trans
        ((hB.some.orderOf_eq b).symm.trans (orderOf_eq_prime_pow (p:=2) (n:=1)
          (by simpa using hbq) (by simpa using htable (hB.some b))))
    let bL : L := ⟨b,hBL b.property⟩
    let aL : L := ⟨a,hBL haB⟩
    have hbL4 : orderOf (eL bL)=4 := by rw [eL.orderOf_eq]; exact (orderOf_injective L.subtype L.subtype_injective bL).symm.trans hb4
    have haL4 : orderOf (eL aL)=4 := by rw [eL.orderOf_eq]; exact (orderOf_injective L.subtype L.subtype_injective aL).symm.trans ha4
    obtain ⟨g,hg⟩ := isConj_iff.mp (GLS3.Chapter5.SchurPresentation.sl23_order_four_isConj (eL bL) (eL aL) hbL4 haL4)
    let gL := eL.symm g
    have hgb : (gL:G)*(b:G)*(gL:G)⁻¹=a := by
      have hh := congrArg eL.symm hg
      simpa only [map_mul,map_inv,eL.symm_apply_apply,coe_mul,coe_inv,gL,bL,aL] using congrArg Subtype.val hh
    have hgy : y*(gL:G)=(gL:G)*y := (hyL gL gL.property).symm
    have hclass : IsConj ((b:G)*y) (a*y) := isConj_iff.mpr ⟨gL,by
      calc
        (gL:G)*((b:G)*y)*(gL:G)⁻¹=(gL:G)*(b:G)*(y*(gL:G)⁻¹) := by group
        _=(gL:G)*(b:G)*((gL:G)⁻¹*y) := by rw [Commute.inv_right (show Commute y (gL:G) from hgy)]
        _=a*y := by rw [←mul_assoc,hgb]⟩
    exact Or.inr (hred.trans hclass)
end Subgroup
