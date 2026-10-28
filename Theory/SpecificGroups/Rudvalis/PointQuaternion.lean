module
public import Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Core

/-!
# Quaternion subgroups in central-class Rudvalis cubic centralizers

The native quaternion is carried back through the original max6 marking.
Since three divides the point-centralizer order only once, Sylow conjugacy
transports it to every cubic. The full involution-centralizer equivalence
then supplies a quaternion in the literal two-core centralizer of any Sylow
three-subgroup of any central-class point centralizer.

All maps retain their actual ambient inclusions. The final Chapter13
odd-actor application combines this order-eight subgroup with the proved
intersection bound of four to obtain an escaping quaternion. Its original
three-space placement remains a separate source obligation.
Source: Aschbacher--Smith J.2.3(7), p.433, and 4.2.13, pp.611--612.
-/

public section
namespace Rudvalis.PointQuaternion
open Subgroup SylowOvergroups
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

private theorem marked_embedding :
    ∃ f : QuaternionGroup 2 →* max6, Function.Injective f ∧
      (∀ a, f a ∈ pCore 2 max6) ∧
      ∀ a, Commute (f a) (⟨CubicElementary.cubic,CubicElementary.cubic_mem⟩ : max6) := by
  let t := MulAut.conj conjugator
  have hcore (a : QuaternionGroup 2) : t.symm (embedding a) ∈ max6.pCoreIn 2 := by
    have hm := map_pCoreIn_of_injective 2 max6 t.toMonoidHom t.injective
    have he := embedding_mem_core a
    rw [←marked_centralizer_eq] at he
    rw [←hm] at he
    obtain ⟨x,hx,he⟩ := he
    have hx' : x = t.symm (embedding a) := by
      apply t.injective
      rw [t.apply_symm_apply]
      exact he
    exact hx' ▸ hx
  let f := (t.symm.toMonoidHom.comp embedding).codRestrict max6
    (fun a => pCoreIn_le 2 max6 (hcore a))
  have hf : Function.Injective f :=
    (MonoidHom.injective_codRestrict _ _ _).mpr
      (t.symm.injective.comp embedding_injective)
  refine ⟨f,hf,?_,?_⟩
  · intro a
    obtain ⟨x,hx,he⟩ := hcore a
    have he' : x = f a := Subtype.ext he
    exact he' ▸ hx
  · intro a
    apply Subtype.ext
    change t.symm (embedding a) * CubicElementary.cubic =
      CubicElementary.cubic * t.symm (embedding a)
    apply t.injective
    rw [map_mul,map_mul,t.apply_symm_apply]
    exact (embedding_commutes a).eq

/-- Every cubic in the native point centralizer has a quaternion subgroup
in its two-core centralizer. -/
theorem exists_embedding_max6 (x : max6) (hx : orderOf x = 3) :
    ∃ f : QuaternionGroup 2 →* max6, Function.Injective f ∧
      (∀ a, f a ∈ pCore 2 max6) ∧ ∀ a, Commute (f a) x := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let c : max6 := ⟨CubicElementary.cubic,CubicElementary.cubic_mem⟩
  have hc : orderOf c = 3 := (Subgroup.orderOf_coe c).symm.trans CubicElementary.cubic_order
  obtain ⟨k,g,hxg⟩ := exists_conjugate_pow_of_orderOf_eq_prime
    (by rw [max6_card]; decide) hx hc
  obtain ⟨f,hf,hcore,hcomm⟩ := marked_embedding
  let t := MulAut.conj g
  refine ⟨t.toMonoidHom.comp f,t.injective.comp hf,?_,?_⟩
  · intro a
    exact Subgroup.Normal.conj_mem (inferInstance : (pCore 2 max6).Normal) (f a) (hcore a) g
  · intro a
    rw [hxg]
    exact ((hcomm a).pow_right k).map t.toMonoidHom

/-- Transport to the literal centralizer of any central-class involution. -/
theorem exists_embedding_point (z : Model) (hz : IsConj z (b^2))
    (x : InvolutionCentralizers.Centralizer z) (hx : orderOf x = 3) :
    ∃ f : QuaternionGroup 2 →* InvolutionCentralizers.Centralizer z,
      Function.Injective f ∧
      (∀ a, f a ∈ pCore 2 (InvolutionCentralizers.Centralizer z)) ∧
      ∀ a, Commute (f a) x := by
  let e := InvolutionCentralizers.firstCentralizerEquiv hz
  obtain ⟨f,hf,hcore,hcomm⟩ := exists_embedding_max6 (e x) ((e.orderOf_eq x).trans hx)
  refine ⟨e.symm.toMonoidHom.comp f,e.symm.injective.comp hf,?_,?_⟩
  · intro a
    have hm := pCore_map_iso 2 e.symm
    rw [←hm]
    exact mem_map_of_mem _ (hcore a)
  · intro a
    have hh := (hcomm a).map e.symm.toMonoidHom
    apply Subtype.ext
    have he := congrArg Subtype.val hh.eq
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using he
/-- The quaternion survives for any actual Sylow three-subgroup of the full
point centralizer, with its original ambient inclusion. -/
theorem exists_quaternion_sylow (z : Model) (hz : IsConj z (b^2))
    (X : Sylow 3 (InvolutionCentralizers.Centralizer z)) :
    ∃ Q : Subgroup Model, Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ≤ (InvolutionCentralizers.Centralizer z).pCoreIn 2 ∧
      Q ≤ centralizer ((X : Subgroup (InvolutionCentralizers.Centralizer z)).map
        (InvolutionCentralizers.Centralizer z).subtype : Set Model) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let D := InvolutionCentralizers.Centralizer z
  have hX : Nat.card X = 3 := by
    rw [X.card_eq_multiplicity,InvolutionCentralizers.first_centralizer_card hz]
    decide +kernel
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hX])
  have hxD : orderOf (x : D) = 3 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨f,hf,hcore,hcomm⟩ := exists_embedding_point z hz x hxD
  let j := D.subtype.comp f
  have hj : Function.Injective j := D.subtype_injective.comp hf
  refine ⟨j.range,⟨(MonoidHom.ofInjective hj).symm⟩,?_,?_⟩
  · rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem D.subtype (hcore a)
  · rintro _ ⟨a,rfl⟩ y ⟨v,hv,rfl⟩
    have hxne : x ≠ 1 := by intro he; rw [he,orderOf_one] at hx; omega
    obtain ⟨k,hk⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hX
      hxne (g' := (⟨v,hv⟩ : X)))
    have hh := congrArg (fun u : X => ((u : D) : Model)) hk
    change (x.val.val)^k = v.val at hh
    change v.val * j a = j a * v.val
    rw [←hh]
    exact (((hcomm a).symm.zpow_left k).map D.subtype).eq

end Rudvalis.PointQuaternion
