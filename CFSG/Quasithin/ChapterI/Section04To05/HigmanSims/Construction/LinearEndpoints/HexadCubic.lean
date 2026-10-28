module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CubicReflectionAction
import Mathlib.GroupTheory.FixedPointFree

/-!
# A second actual cubic inverted by the original endpoint reflection

The unique Sylow three-subgroup of the order-eighteen normalizer centralizer
has order nine. The same endpoint reflection acts on it without nonidentity
fixed points and therefore by inversion. Its faithful six-letter action
excludes order nine. A cubic outside the original torus lies in the literal
even hexad preimage. No Mathieu completion or index hypothesis is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} [IsElementaryAbelian 2 A]

private theorem six_letter_ninth_cube (a : Equiv.Perm (Fin 6)) (ha : a^9=1) :
    a^3=1 := by
  apply Equiv.Perm.pow_prime_eq_one_iff.mpr
  intro n hn
  have hd : n∣9 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one ha)
  have hlo := Equiv.Perm.two_le_of_mem_cycleType hn
  have hhi : n≤6 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    (by simpa using Finset.card_le_univ a.support)
  interval_cases n <;> omega

private theorem cube_even (a : Equiv.Perm (Fin 6)) (ha : a^3=1) :
    Equiv.Perm.sign a=1 := by
  have hs := congrArg Equiv.Perm.sign ha
  rw [map_pow,map_one] at hs
  rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h
  · exact h
  · rw [h] at hs
    norm_num at hs

/-- The specified actual endpoint reflection inverts a second cubic in
the literal hexad overgroup, outside the original cubic subgroup. -/
theorem NaturalEndpointData.exists_inverted_hexad_cubic (d : NaturalEndpointData A)
    (t r : G) (ht : t∈d.carrier) (ht3 : orderOf t=3)
    (hr : r∈d.carrier) (hr2 : orderOf r=2) (hinv : r*t*r⁻¹=t⁻¹) :
    ∃ n : G, n∈d.hexad_overgroup ∧ Commute n t ∧ orderOf n=3 ∧
      n∉zpowers t ∧ r*n*r⁻¹=n⁻¹ := by
  classical
  let E := normalizer (A : Set G)⊓centralizer ({t} : Set G)
  obtain ⟨hE18,f,_,_,_,e,_⟩ := d.cubic_full_normalizer_centralizer t ht ht3
  obtain ⟨hrE,hfix2,_⟩ := d.cubic_reflection_action t r ht ht3 hr hr2 hinv
  let S : Sylow 3 E := Classical.choice inferInstance
  have hS9 : Nat.card S=9 := by
    rw [S.card_eq_multiplicity,hE18]
    decide +kernel
  have hSindex : (S : Subgroup E).index=2 := by
    have hh := (S : Subgroup E).card_mul_index
    rw [hS9,hE18] at hh
    omega
  have hSn : (S : Subgroup E).Normal := normal_of_index_eq_two hSindex
  let : (S : Subgroup E).Characteristic := S.characteristic_of_normal hSn
  let α : MulAut E := E.normalizerMonoidHom ⟨r,hrE⟩
  let β : MulAut S := MulAut.characteristic (S : Subgroup E) α
  have hα2 : α^2=1 := by
    change (E.normalizerMonoidHom ⟨r,hrE⟩)^2=1
    rw [←map_pow]
    have hh : (⟨r,hrE⟩ : normalizer (E : Set G))^2=1 := by
      apply Subtype.ext
      change r^2=1
      simpa only [hr2] using pow_orderOf_eq_one r
    rw [hh,map_one]
  have hβ2 : β^2=1 := by
    change (MulAut.characteristic (S : Subgroup E) α)^2=1
    rw [←map_pow,hα2,map_one]
  have hfree : MonoidHom.FixedPointFree β.toMonoidHom := by
    intro x hx
    have hxr : (x : G)∈centralizer ({r} : Set G) := by
      have hh := congrArg (fun y : S => (y : G)) hx
      change r*(x : G)*r⁻¹=(x : G) at hh
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hd2 := orderOf_dvd_natCard
      (⟨x,⟨(x : E).property,hxr⟩⟩ : (E⊓centralizer ({r} : Set G) : Subgroup G))
    have hd9 := orderOf_dvd_natCard x
    rw [←orderOf_coe,hfix2] at hd2
    rw [hS9,←orderOf_coe x,←orderOf_coe (x : E)] at hd9
    have ho : orderOf (x : G)=1 := Nat.eq_one_of_dvd_coprimes
      (by decide : Nat.Coprime 2 9) hd2 hd9
    apply Subtype.ext
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp ho
  have hinverts (x : S) : r*(x : G)*r⁻¹=(x : G)⁻¹ := by
    have hh := congrFun (hfree.coe_eq_inv_of_involutive (fun y =>
      DFunLike.congr_fun hβ2 y)) x
    exact congrArg (fun y : S => (y : G)) hh
  let F : Subgroup G := (S : Subgroup E).map E.subtype
  have hF9 : Nat.card F=9 := (card_map_of_injective E.subtype_injective).trans hS9
  have hnot : ¬F≤zpowers t := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hF9,Nat.card_zpowers,ht3] at hc
    omega
  obtain ⟨n,hnF,hnT⟩ := Set.not_subset.mp hnot
  obtain ⟨nE,hnS,rfl⟩ := hnF
  let n : S := ⟨nE,hnS⟩
  have hn9 : nE^9=1 := by
    have hh := pow_card_eq_one' (x:=n)
    change n ^ Nat.card (S : Subgroup E) = 1 at hh
    rw [hS9] at hh
    exact congrArg (fun x : S => (x : E)) hh
  have hn3 : nE^3=1 := by
    apply e.injective
    apply Subtype.ext
    simpa only [map_pow,map_one,coe_pow,coe_one] using six_letter_ninth_cube (e nE : Equiv.Perm (Fin 6))
      (by simpa only [map_pow,map_one,coe_pow,coe_one] using
        congrArg (fun x : E => (e x : Equiv.Perm (Fin 6))) hn9)
  have hnG3 : (nE : G)^3=1 := congrArg Subtype.val hn3
  have hn1 : (nE : G)≠1 := by
    intro he
    apply hnT
    change (nE : G)∈zpowers t
    rw [he]
    exact (zpowers t).one_mem
  have hnD : (nE : G)∈d.hexad_overgroup := by
    let nN : normalizer (A : Set G) := ⟨nE,nE.property.1⟩
    change (normalizer (A : Set G)).subtype nN ∈
      ((alternatingGroup (Fin 6)).comap d.six_letter_quotient).map
        (normalizer (A : Set G)).subtype
    apply mem_map_of_mem (normalizer (A : Set G)).subtype
    apply Equiv.Perm.mem_alternatingGroup.mpr
    apply cube_even
    rw [←map_pow]
    have hh : nN^3=1 := Subtype.ext hnG3
    rw [hh,map_one]
  exact ⟨nE,hnD,mem_centralizer_singleton_iff.mp nE.property.2,
    orderOf_eq_prime hnG3 hn1,hnT,hinverts n⟩

end CFSG.Quasithin.HigmanSims
