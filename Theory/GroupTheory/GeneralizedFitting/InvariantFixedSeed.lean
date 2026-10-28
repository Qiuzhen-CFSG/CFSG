module
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupAction.AutomorphismFixedSubgroup
/-!
# The actual involution on an invariant containing component

A component of C_G(t) lying in a t-invariant ambient component remains a
component of the literal fixed subgroup of conjugation on that component.
If the seed is not itself an ambient component, this conjugation is nontrivial:
otherwise subnormal ascent would make the seed an ambient component.

The theorem keeps the action on every element, so model inspections use the
original t. Source: Aschbacher–Smith I.3.2 and 2.5.19, pp.414–415 and 560–561.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G:Type*} [Group G]

/-- Restrict original conjugation to the invariant component and its fixed seed. -/
theorem invariant_component_fixed_seed {K X:Subgroup G} (t:G) (ht:orderOf t=2)
    (hK:IsComponentIn K (centralizer ({t}:Set G)))
    (hX:IsComponent G X) (hKX:K≤X)
    (hfix:X.map (MulAut.conj t).toMonoidHom=X) (hnot:¬IsComponent G K) :
    ∃a:MulAut X, orderOf a=2 ∧
      (∀x:X,(a x:G)=t*(x:G)*t⁻¹) ∧
      IsComponentIn (K.subgroupOf X) a.fixedSubgroup := by
  have htN:t∈normalizer (X:Set G):=mem_normalizer_iff_map_conj_eq.mpr hfix
  let tN:normalizer (X:Set G):=⟨t,htN⟩
  let a:=X.normalizerMonoidHom tN
  have ha (x:X):(a x:G)=t*(x:G)*t⁻¹:=rfl
  have han:a≠1 := by
    intro he
    have hXC:X≤centralizer ({t}:Set G) := by
      intro x hx
      have hxfix:=ha ⟨x,hx⟩
      rw [he] at hxfix
      change x=t*x*t⁻¹ at hxfix
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp hxfix.symm).symm
    have hKXin:=hK.restrict hKX hXC
    exact hnot ⟨Subgroup.IsSubnormal.trans hKX hKXin.2.1 hX.1,hK.quasisimple⟩
  have ha2:a^2=1 := by
    change X.normalizerMonoidHom tN^2=1
    rw [←map_pow]
    have htN2:tN^2=1:=by
      apply Subtype.ext
      change t^2=1
      rw [←ht]
      exact pow_orderOf_eq_one t
    rw [htN2,map_one]
  have hKD:K.subgroupOf X≤a.fixedSubgroup := by
    intro k hk
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [ha]
    have hc:=mem_centralizer_singleton_iff.mp (hK.1 hk)
    change (k:G)*t=t*(k:G) at hc
    rw [←hc,mul_inv_cancel_right]
  let Ct:=centralizer ({t}:Set G)
  let f:a.fixedSubgroup→*Ct:=
    (X.subtype.comp a.fixedSubgroup.subtype).codRestrict Ct (fun x=>by
      apply mem_centralizer_singleton_iff.mpr
      have he:=congrArg (fun y:X=>(y:G)) ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
      rw [ha] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm)
  let L:Subgroup a.fixedSubgroup:=(K.subgroupOf X).subgroupOf a.fixedSubgroup
  let e:L≃*K:=(subgroupOfEquivOfLe hKD).trans (subgroupOfEquivOfLe hKX)
  have hL:IsComponent a.fixedSubgroup L := by
    refine ⟨hK.2.1.comap f,?_⟩
    let : IsQuasisimple K:=hK.quasisimple
    exact IsQuasisimple.of_mulEquiv e.symm
  exact ⟨a,orderOf_eq_prime ha2 han,ha,hKD,hL⟩
end Theory.GroupTheory
