module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow

/-!
# The odd core detected by a quaternion Sylow involution

All involutions in a quaternion-Sylow group are conjugate. A normal subgroup
avoiding the marked involution therefore has odd order. Applied to the
centralizer of the odd core, this makes that core self-centralizing when
the marked involution moves it. If the odd core has order243 it is O3,
and hence is the entire generalized Fitting subgroup.
Source: Aschbacher, Sporadic Groups (1994),45.8,printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem odd_of_normal_avoids_quaternion_involution (P:Sylow 2 G)
    (e:P≃*QuaternionGroup 4) (z:G) (hzP:z∈P) (hz:orderOf z=2)
    (K:Subgroup G) [K.Normal] (hzK:z∉K) : Odd (Nat.card K) := by
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨t,ht⟩:=exists_prime_orderOf_dvd_card' (G:=K) 2 hd
  have htG:orderOf (t:G)=2:=(orderOf_injective K.subtype K.subtype_injective t).trans ht
  have hp:IsPGroup 2 (zpowers (t:G)):=IsPGroup.of_card (n:=1) (by simp [Nat.card_zpowers,htG])
  obtain ⟨Q,hQ⟩:=hp.exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G Q P
  have hgt:g*(t:G)*g⁻¹∈P:=by
    rw [←hg]
    exact (Q.equivSMul g ⟨t,hQ (mem_zpowers (t:G))⟩).property
  have hgo:orderOf (g*(t:G)*g⁻¹)=2:=
    (MulEquiv.orderOf_eq (MulAut.conj g) (t:G)).trans htG
  have huniq (x:P) (hx:orderOf x=2): e x=QuaternionGroup.a 4:=by
    have ho:orderOf (e x)=2:=(e.orderOf_eq x).trans hx
    have hn:e x≠1:=by intro hh;simp [hh] at ho
    have hs:(e x)^2=1:=by simpa only [ho] using pow_orderOf_eq_one (e x)
    exact (by decide:∀y:QuaternionGroup 4,y≠1→y^2=1→y=QuaternionGroup.a 4) _ hn hs
  have he:g*(t:G)*g⁻¹=z:=congrArg Subtype.val (e.injective
    ((huniq ⟨_,hgt⟩ (by rwa [orderOf_mk])).trans
      (huniq ⟨z,hzP⟩ (by rwa [orderOf_mk])).symm))
  exact hzK (he ▸ (inferInstance:K.Normal).conj_mem t t.property g)

theorem oddCore_centralizer_le_of_quaternion_sylow (P:Sylow 2 G)
    (e:P≃*QuaternionGroup 4) (z:G) (hzP:z∈P) (hz:orderOf z=2)
    (hmove:z∉centralizer (pPrimeCore 2 G:Set G)) :
    centralizer (pPrimeCore 2 G:Set G)≤pPrimeCore 2 G := by
  have ho:=odd_of_normal_avoids_quaternion_involution P e z hzP hz
    (centralizer (pPrimeCore 2 G:Set G)) hmove
  exact le_sSup ⟨inferInstance,Nat.coprime_two_left.mpr ho⟩

theorem generalizedFitting_eq_oddCore_of_quaternion_sylow (P:Sylow 2 G)
    (e:P≃*QuaternionGroup 4) (z:G) (hzP:z∈P) (hz:orderOf z=2)
    (hmove:z∉centralizer (pPrimeCore 2 G:Set G))
    (hD:Nat.card (pPrimeCore 2 G)=243) : Theory.GroupTheory.generalizedFitting G=pPrimeCore 2 G := by
  have hp:IsPGroup 3 (pPrimeCore 2 G):=IsPGroup.of_card (n:=5) hD
  have hDP:pPrimeCore 2 G≤pCore 3 G:=le_sSup ⟨inferInstance,hp⟩
  have hPD:pCore 3 G≤pPrimeCore 2 G:=by
    apply le_sSup
    refine ⟨inferInstance,?_⟩
    obtain ⟨n,hn⟩:=(pCore_isPGroup (p:=3) (G:=G)).exists_card_eq
    rw [hn]
    exact (by decide:Nat.Coprime 2 3).pow_right n
  have hEq:pCore 3 G=pPrimeCore 2 G:=le_antisymm hPD hDP
  rw [←hEq]
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 3
  rw [hEq]
  exact oddCore_centralizer_le_of_quaternion_sylow P e z hzP hz hmove
end Subgroup
