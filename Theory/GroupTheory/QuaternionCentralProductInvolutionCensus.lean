module
public import Theory.GroupTheory.QuaternionCentralProductSingularGrid
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Eighteen noncentral involutions in the quaternion central product

The nine singular central cosets each have two lifts. A chosen representative
gives an explicit bijection from singular cosets times the actual center to
the noncentral involutions. The companion orbit–stabilizer formula applies to
an actual normal core in an overgroup transitive on these involutions.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.2(4), printed p. 242.
-/

open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

include d in
public theorem noncentral_involutions_card :
    Nat.card {x : Q // orderOf x = 2 ∧ x ∉ center Q} = 18 := by
  classical
  let S := CentralInvolutionCosets Q
  let Z := center Q
  let q := QuotientGroup.mk' Z
  let r : S → Q := fun v => v.property.2.choose
  have hr (v : S) : r v ^ 2 = 1 ∧ q (r v) = v.val := v.property.2.choose_spec
  let X := {x : Q // orderOf x = 2 ∧ x ∉ center Q}
  have hrZ (v : S) : r v ∉ Z := by
    intro hv
    exact v.property.1 ((hr v).2.symm.trans ((QuotientGroup.eq_one_iff (r v)).mpr hv))
  have hm (v : S) (c : Z) : r v * c ∉ Z := by
    intro hc
    exact hrZ v (by simpa using Z.mul_mem hc (Z.inv_mem c.property))
  let f : S × Z → X := fun p => ⟨r p.1 * p.2,
    orderOf_eq_prime (by
      rw [(show Commute (r p.1) (p.2 : Q) from mem_center_iff.mp p.2.property _).mul_pow,
        (hr p.1).1, (show (p.2:Q)^2=1 from congrArg Subtype.val (d.center_square p.2)), one_mul])
      (fun h => hm p.1 p.2 (h ▸ Z.one_mem)), hm p.1 p.2⟩
  have hf (v : S) (c : Z) : q (f (v,c)) = v.val := by
    change q (r v * c) = v.val
    rw [map_mul,(show q (c:Q) = 1 from (QuotientGroup.eq_one_iff (c:Q)).mpr c.property),mul_one,(hr v).2]
  have hi : Function.Injective f := by
    rintro ⟨v,c⟩ ⟨w,e⟩ he
    have hvw : v = w := Subtype.ext (by rw [← hf v c,← hf w e,he])
    subst w
    have hc : (c : Q) = e := mul_left_cancel (congrArg Subtype.val he)
    exact Prod.ext rfl (Subtype.ext hc)
  have hs : Function.Surjective f := by
    intro x
    let v : S := centralInvolutionCoset x.val
      (by have hh := pow_orderOf_eq_one x.val; rwa [x.property.1] at hh) x.property.2
    have hc : (r v)⁻¹ * x.val ∈ Z := QuotientGroup.eq.mp (hr v).2
    refine ⟨(v,⟨(r v)⁻¹*x.val,hc⟩),Subtype.ext ?_⟩
    exact mul_inv_cancel_left (r v) x.val
  have hS : Nat.card S = 9 := by
    rw [← Nat.card_congr d.singularProduct, Nat.card_prod,
      d.factorPoints_card d.left (Or.inl rfl),d.factorPoints_card d.right (Or.inr rfl)]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_prod,hS,d.center_card]

public theorem card_centralizer_mul_eighteen_of_transitive
    {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [Q.Normal]
    (d : QuaternionCentralProductData Q)
    (htrans : ∀ x y : Q, orderOf x = 2 → x ∉ center Q →
      orderOf y = 2 → y ∉ center Q → IsConj (x : H) (y : H))
    (u : Q) (hu : orderOf u = 2) (huZ : u ∉ center Q) :
    Nat.card (centralizer ({(u : H)} : Set H)) * 18 = Nat.card H := by
  let T := {x : Q // orderOf x = 2 ∧ x ∉ center Q}
  let O := MulAction.orbit (ConjAct H) (u : H)
  let f : T → O := fun x => ⟨x.val, ConjAct.mem_orbit_conjAct.mpr
    (htrans x.val u x.property.1 x.property.2 hu huZ)⟩
  have hi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun t : O => (t:H)) he))
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨g,hg⟩ := isConj_iff.mp (ConjAct.mem_orbit_conjAct.mp x.property).symm
    let a : MulAut Q := MulAut.conjNormal g
    have ha : orderOf (a u) = 2 := (a.orderOf_eq u).trans hu
    have haZ : a u ∉ center Q := fun hc => huZ ((MulEquivClass.apply_mem_center_iff a).mp hc)
    exact ⟨⟨a u,ha,haZ⟩,Subtype.ext hg⟩
  have hO : Nat.card O = 18 :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans d.noncentral_involutions_card
  have hstab : Nat.card (centralizer ({(u : H)} : Set H)) =
      Nat.card (MulAction.stabilizer (ConjAct H) (u : H)) := by
    rw [centralizer_eq_comap_stabilizer]
    rfl
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) (u : H))
  rw [Nat.card_prod,← hstab,hO,Nat.mul_comm] at he
  exact he
end Subgroup.QuaternionCentralProductData
