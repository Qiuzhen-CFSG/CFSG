module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightCubicInverter
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.ElementaryAbelian.Basic

/-!
# Fixed points of a cubic quaternion actor

A nontrivial cubic on Q8 has a commutator whose square is the central
involution. If that involution inverts a ternary section, the fixed groups
of the cubic and one quaternion conjugate intersect trivially. Their product
embeds in the section, so the square of the fixed-group order is at most
the section order. The last theorem retains the actual intertwining action,
without assuming a linear representation or module classification.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section
open Subgroup
namespace QuaternionGroup
open GLS3.Chapter5.SchurPresentation
theorem exists_cubic_commutator_square (c:MulAut (QuaternionGroup 2)) (hc:c^3=1) (hne:c≠1)
    (z:QuaternionGroup 2) (hz:orderOf z=2) : ∃q:QuaternionGroup 2,(c q*q⁻¹)^2=z := by
  obtain ⟨e,he⟩:=Subgroup.QuaternionCubicAction.exists_coordinates c hc hne
  have hz':e z=QuaternionGroup.a 2:=by
    have ho:orderOf (e z)=2:=(e.orderOf_eq z).trans hz
    have hn:e z≠1:=by intro hh;simp [hh] at ho
    have hp:(e z)^2=1:=by simpa only [ho] using pow_orderOf_eq_one (e z)
    exact (by decide:∀x:QuaternionGroup 2,x≠1→x^2=1→x=QuaternionGroup.a 2) _ hn hp
  refine ⟨e.symm (QuaternionGroup.a 1),e.injective ?_⟩
  rw [map_pow,map_mul,map_inv,MulEquiv.apply_symm_apply,hz']
  have hh:=DFunLike.congr_fun he (QuaternionGroup.a 1)
  change e (c (e.symm (QuaternionGroup.a 1)))=q8Cycle (QuaternionGroup.a 1) at hh
  rw [hh]
  decide
end QuaternionGroup

namespace MulAut
variable {A:Type*} [Group A] [Finite A]
theorem fixed_card_square_le_of_conjugate_inverse_product (hA:IsPGroup 3 A)
    (a b:MulAut A) (hi:∀x,((a*(b*a⁻¹*b⁻¹))^2) x=x⁻¹) :
    Nat.card a.fixedSubgroup^2≤Nat.card A := by
  let c:=b*a⁻¹*b⁻¹
  have hd:Disjoint a.fixedSubgroup c.fixedSubgroup:=by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    have ha:a x=x:=(mem_fixedSubgroup a x).mp hx
    have hc:c x=x:=(mem_fixedSubgroup c x).mp hy
    have ht:(a*c) x=x:=by change a (c x)=x;rw [hc,ha]
    have hs:((a*c)^2) x=x:=by change a (c (a (c x)))=x;rw [hc,ha,hc,ha]
    have hin:x⁻¹=x:=(hi x).symm.trans hs
    have hp:x^2=1:=(pow_two x).trans (inv_eq_iff_mul_eq_one.mp hin)
    by_contra hn
    have hh:3∣2:=(hA.dvd_orderOf hn).trans (orderOf_dvd_of_pow_eq_one hp)
    norm_num at hh
  have hcard:Nat.card c.fixedSubgroup=Nat.card a.fixedSubgroup:=by
    have hc:c=MulAut.congr b a⁻¹:=by ext x;rfl
    rw [hc,Nat.card_congr (fixedSubgroupCongr b a⁻¹).symm.toEquiv]
    have he:(a⁻¹).fixedSubgroup=a.fixedSubgroup:=by
      ext x
      rw [mem_fixedSubgroup,mem_fixedSubgroup]
      change a.symm x=x ↔ a x=x
      constructor
      · intro h
        simpa only [a.apply_symm_apply] using (congrArg a h).symm
      · intro h
        simpa only [a.symm_apply_apply] using (congrArg a.symm h).symm
    rw [he]
  have hinj:Function.Injective (fun p:a.fixedSubgroup×c.fixedSubgroup=>(p.1:A)*(p.2:A)):=
    mul_injective_of_disjoint hd
  have hbound:=Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod,hcard,←pow_two] at hbound
end MulAut

namespace MulAut
variable {Q A:Type*} [Group Q] [Group A] [Finite A]
theorem quaternion_cubic_fixed_card_bound (e:Q≃*QuaternionGroup 2)
    (c:MulAut Q) (hc:c^3=1) (hne:c≠1) (z:Q) (hz:orderOf z=2)
    (hA:IsPGroup 3 A) (σ:Q→*MulAut A) (a:MulAut A)
    (hcompat:∀q,a*σ q*a⁻¹=σ (c q)) (hzact:∀x,σ z x=x⁻¹) :
    Nat.card a.fixedSubgroup^2≤Nat.card A := by
  let φ:=MulAut.congr e
  obtain ⟨v,hv⟩:=QuaternionGroup.exists_cubic_commutator_square (φ c)
    (by rw [←map_pow,hc,map_one]) (fun hh=>hne (φ.injective (hh.trans φ.map_one.symm)))
    (e z) (by rw [e.orderOf_eq];exact hz)
  let q:Q:=e.symm v
  have hq:(c q*q⁻¹)^2=z:=by
    apply e.injective
    rw [map_pow,map_mul,map_inv]
    change (e (c (e.symm v))*v⁻¹)^2=e z at hv
    simpa only [q,MulEquiv.apply_symm_apply] using hv
  apply fixed_card_square_le_of_conjugate_inverse_product hA a (σ q)
  intro x
  have he:a*(σ q*a⁻¹*(σ q)⁻¹)=σ (c q*q⁻¹):=by
    rw [map_mul,map_inv,←hcompat q]
    group
  rw [he,←map_pow,hq]
  exact hzact x
end MulAut
