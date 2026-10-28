module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Action
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Actors
public import Mathlib.Tactic.Group

/-!
# Cubic lifts through the actual cyclic center

A central kernel of order four makes the fourth power of any lift a genuine
cubic lift, and two cubic lifts with the same image coincide. Applied to the
surjective quaternion action, this constructs a cubic and an outer inverter
whose square is central, with exact inversion on the original elements.

Source: Aschbacher–Smith F.1.12(I)(8), nonabelian order-96 vertex.
-/
@[expose] public section

noncomputable section
open Subgroup
namespace WreathedVertex
variable {G H:Type*} [Group G] [Group H]

theorem center_fourth (hZ:Nat.card (center G)=4) (z:G) (hz:z∈center G) : z^4=1 := by
  have h: (⟨z,hz⟩:center G)^4=1 := by rw [←hZ];exact pow_card_eq_one'
  exact congrArg Subtype.val h

theorem lift_cubic (f:G→*H) (hf:Function.Surjective f) (hk:f.ker=center G)
    (hZ:Nat.card (center G)=4) (a:H) (ha:a^3=1) :
    ∃c:G,c^3=1∧f c=a := by
  obtain ⟨b,hb⟩:=hf a
  have hcentral:b^3∈center G := by
    rw [←hk,MonoidHom.mem_ker,map_pow,hb,ha]
  have h12:=center_fourth hZ (b^3) hcentral
  refine ⟨b^4,?_,?_⟩
  · simpa only [←pow_mul] using h12
  · rw [map_pow,hb,show 4=3+1 from rfl,pow_succ,ha,one_mul]

theorem cubic_lifts_unique (f:G→*H) (hk:f.ker=center G)
    (hZ:Nat.card (center G)=4) (x y:G) (hx:x^3=1) (hy:y^3=1) (he:f x=f y) : x=y := by
  let z:=x*y⁻¹
  have hz:z∈center G := by
    rw [←hk,MonoidHom.mem_ker]
    simp only [z,map_mul,map_inv,he,mul_inv_cancel]
  have hc:Commute z y := (mem_center_iff.mp hz y).symm
  have hz3:z^3=1 := by
    have hh: (z*y)^3=1 := by simpa only [z,inv_mul_cancel_right] using hx
    rw [hc.mul_pow,hy,mul_one] at hh
    exact hh
  have hz4:=center_fourth hZ z hz
  have he1:z=1:=orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide:Nat.Coprime 3 4)
    (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_of_pow_eq_one hz4))
  exact mul_inv_eq_one.mp he1

theorem lift_quaternion_actors [Finite G] (Q:Subgroup G) [Q.Normal]
    (e:Q≃*QuaternionCyclic.Model) (hG:Nat.card G=96)
    (hc:centralizer (Q:Set G)≤Q) (hz:(center Q).map Q.subtype≤center G)
    (hZ:Nat.card (center G)=4) :
    ∃c v:G,orderOf c=3∧quaternionAction Q e c=QuaternionCyclic.quaternionCubic∧
      quaternionAction Q e v=quaternionInverter∧v^2∈center G∧v^8=1∧
      v*c*v⁻¹=c⁻¹ := by
  let f:=quaternionAction Q e
  have hf:=quaternionAction_surjective Q e hG hc hz hZ
  have hk:=quaternionAction_ker Q e hc hz
  obtain ⟨c,hc3,hfc⟩:=lift_cubic f hf hk hZ _ QuaternionCyclic.quaternionCubic_cube
  obtain ⟨v,hfv⟩:=hf quaternionInverter
  have hco:orderOf c=3 := by
    apply orderOf_eq_prime hc3
    intro he
    have h:=congrArg orderOf hfc
    rw [he,map_one,orderOf_one,quaternionCubic_order] at h
    omega
  have hv2:v^2∈center G := by
    rw [←hk,MonoidHom.mem_ker,map_pow,hfv,quaternionInverter_square]
  have hv8:v^8=1:=by simpa only [←pow_mul] using center_fourth hZ (v^2) hv2
  refine ⟨c,v,hco,hfc,hfv,hv2,hv8,?_⟩
  apply cubic_lifts_unique f hk hZ
  · rw [conj_pow,hc3,mul_one,mul_inv_cancel]
  · rw [inv_pow,hc3,inv_one]
  · rw [map_mul,map_mul,map_inv,map_inv,hfc,hfv,quaternionInverter_inverts]
end WreathedVertex
