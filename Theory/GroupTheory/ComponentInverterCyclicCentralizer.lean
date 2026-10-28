module
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.OuterPGroupSylowSupplement
/-!
# A component involution and a cyclic centralizer Sylow

A component containing the involution that inverts the odd core forces
that odd core to be trivial: the component-normal-subgroup dichotomy gives
centralization, and odd order rules out nontrivial squares equal to one.
A cyclic Sylow in the component centralizer then has trivial odd complement,
so the centralizer lies in the supplied Sylow. A two-group outer quotient
therefore gives generation by the component and that Sylow.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem oddCore_eq_bot_of_component_involution_inverts
    (K : Subgroup G) (hK : IsComponent G K) (z : G) (hzK : z∈K) (hz : orderOf z=2)
    (hinv : ∀u∈pPrimeCore 2 G,z*u*z⁻¹=u⁻¹) : pPrimeCore 2 G=⊥ := by
  have hn : ¬ K≤pPrimeCore 2 G := by
    intro h
    have hd : 2∣Nat.card (pPrimeCore 2 G) := hz ▸ (pPrimeCore 2 G).orderOf_dvd_natCard (h hzK)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p:=2) (G:=G))) hd
  have hc : K≤centralizer (pPrimeCore 2 G:Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hK.normal_dichotomy (pPrimeCore 2 G)).resolve_left hn)
  apply bot_unique
  intro u hu
  have hsq : u^2=1 := by
    have hh := hinv u hu
    rw [←hc hzK u hu,mul_inv_cancel_right] at hh
    calc u^2=u*u := pow_two u
         _ = u*u⁻¹ := congrArg (u * ·) hh
         _ = 1 := mul_inv_cancel u
  have hd2 : orderOf u∣2 := orderOf_dvd_of_pow_eq_one hsq
  have hdO := (pPrimeCore 2 G).orderOf_dvd_natCard hu
  have ho : orderOf u=1 := Nat.eq_one_of_dvd_coprimes (pPrimeCore_coprime_card (p:=2) (G:=G)) hd2 hdO
  exact mem_bot.mpr (orderOf_eq_one_iff.mp ho)

theorem normal_centralizer_le_sylow_of_cyclic_restriction
    (K : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hcyc : IsCyclic ((P : Subgroup G).subgroupOf (centralizer (K:Set G))))
    (heven : 2∣Nat.card (centralizer (K:Set G))) (hodd : pPrimeCore 2 G=⊥) :
    centralizer (K:Set G)≤P := by
  let C := centralizer (K:Set G)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal C
  have hQC : IsCyclic Q := by rw [hQ];exact hcyc
  have hO : pPrimeCore 2 C=⊥ := by
    have hm : (pPrimeCore 2 C).map C.subtype=⊥ := by
      apply pPrimeCore_eq_bot_iff.mp hodd
      · infer_instance
      · rw [card_map_of_injective C.subtype_injective]
        exact pPrimeCore_coprime_card
    exact map_injective C.subtype_injective (by simpa only [Subgroup.map_bot] using hm)
  have htop : (Q : Subgroup C)=⊤ := by
    have hh := (Q.isComplement'_pPrimeCore_of_isCyclic hQC heven).sup_eq_top
    simpa only [hO,sup_bot_eq] using hh
  intro a ha
  have hqa : (⟨a,ha⟩ : C)∈(Q:Subgroup C) := by rw [htop];exact mem_top _
  rw [hQ] at hqa
  exact hqa

theorem normal_sylow_sup_eq_top_of_cyclic_centralizer_restriction
    (K : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hout : IsPGroup 2 (MulAut.Outer K))
    (hcyc : IsCyclic ((P : Subgroup G).subgroupOf (centralizer (K:Set G))))
    (heven : 2∣Nat.card (centralizer (K:Set G))) (hodd : pPrimeCore 2 G=⊥) :
    K⊔(P : Subgroup G)=⊤ := by
  have hc := normal_centralizer_le_sylow_of_cyclic_restriction K P hcyc heven hodd
  apply top_unique
  rw [← normal_centralizer_sup_sylow_eq_top K P hout]
  exact sup_le (sup_le le_sup_left (hc.trans le_sup_right)) le_sup_right
end Theory.GroupTheory
