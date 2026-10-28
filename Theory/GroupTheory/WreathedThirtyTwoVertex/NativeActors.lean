module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Lifts
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Squares

/-!
# Actual marked actors for the nonabelian wreathed vertex

Lift a fixed cubic and outer reflection through the full quaternion action.
The Sylow central-square calculation excludes fourth power one for the outer
lift, so its square generates the core center. Replacing the lift by its
inverse if needed makes that square the specified central generator while
preserving both the reflection action and inversion of the cubic.

Source: Aschbacher–Smith F.1.12(I)(8), nonabelian order-96 vertex.
-/
@[expose] public section

noncomputable section
open Subgroup
namespace WreathedVertex
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
theorem coreAction_core (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model) (a:Q) :
    coreAction Q e (a:G)=MulAut.conj (e a) := by
  apply MulEquiv.ext
  intro x
  change e (MulAut.conjNormal (a:G) (e.symm x))=e a*x*(e a)⁻¹
  have hh:MulAut.conjNormal (a:G) (e.symm x)=a*e.symm x*a⁻¹:=Subtype.ext rfl
  rw [hh,map_mul,map_mul,map_inv,e.apply_symm_apply]

omit [Finite G] in
theorem quaternionAction_core (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model) (a:Q) :
    quaternionAction Q e (a:G)=MulAut.conj (e a).quaternion := by
  change QuaternionCyclic.restrictionHom (coreAction Q e (a:G))=_
  rw [coreAction_core,QuaternionCyclic.conj_eq_extendAut]
  exact QuaternionCyclic.restrictionHom_extendAutHom _

theorem native_actors (Q:Subgroup G) [Q.Normal]
    (hQ:IsPGroup 2 Q) (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q)
    (hG:Nat.card G=96) (S:Sylow 2 G) (eS:S≃*W) (e:Q≃*QuaternionCyclic.Model) :
    ∃c v:G,orderOf c=3∧quaternionAction Q e c=QuaternionCyclic.quaternionCubic∧
      quaternionAction Q e v=quaternionInverter∧
      v^2=(e.symm QuaternionCyclic.r:G)∧v*c*v⁻¹=c⁻¹ := by
  have h3:3∣Nat.card G:=by rw [hG];decide
  have hz:=core_center_central Q hQ hc hna h3 S eS
  have hZ:=center_card_four Q hQ hc hna h3 S eS
  obtain ⟨c,v,hco,hfc,hfv,hv2,_,hvc⟩:=lift_quaternion_actors Q e hG hc hz hZ
  have hvQ:v∉Q := by
    intro hh
    apply quaternionInverter_not_inner
    exact ⟨(e ⟨v,hh⟩).quaternion,(quaternionAction_core Q e ⟨v,hh⟩).symm.trans hfv⟩
  have hv4:v^4≠1 := fun hh=>hvQ (source_fourth_one_central_square_mem Q hQ hc hna h3 S eS v hh hv2)
  have hv2Q:v^2∈Q:=hc (center_le_centralizer (Q:Set G) hv2)
  let a:Q:=⟨v^2,hv2Q⟩
  have ha:a∈center Q:=mem_center_iff.mpr (fun b=>Subtype.ext (mem_center_iff.mp hv2 b))
  have hec:e a∈center QuaternionCyclic.Model:=(centerCongr e ⟨a,ha⟩).property
  have hea:(e a)^2≠1 := by
    intro hh
    have ht:a^2=1:=e.injective (by simpa only [map_pow,map_one] using hh)
    exact hv4 (by simpa only [a,coe_pow,coe_mk,coe_one,←pow_mul] using congrArg Subtype.val ht)
  have cases:∀a:QuaternionCyclic.Model,(∀b:QuaternionCyclic.Model,b*a=a*b)→a^2≠1→
      a=QuaternionCyclic.r∨a=QuaternionCyclic.r⁻¹ := by decide +kernel
  rcases cases _ (mem_center_iff.mp hec) hea with he|he
  · refine ⟨c,v,hco,hfc,hfv,?_,hvc⟩
    have ht:a=e.symm QuaternionCyclic.r:=e.injective (by rw [he,e.apply_symm_apply])
    exact congrArg (fun x:Q=>(x:G)) ht
  · have hvinv:quaternionAction Q e v⁻¹=quaternionInverter := by
      rw [map_inv,hfv]
      exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using quaternionInverter_square)
    refine ⟨c,v⁻¹,hco,hfc,hvinv,?_,?_⟩
    · have ht:a=(e.symm QuaternionCyclic.r)⁻¹:=e.injective (by rw [map_inv,he,e.apply_symm_apply])
      have hh:=congrArg (fun x:Q=>(x:G)) ht
      change v^2=(e.symm QuaternionCyclic.r:G)⁻¹ at hh
      rw [inv_pow,hh,inv_inv]
    · apply cubic_lifts_unique (quaternionAction Q e) (quaternionAction_ker Q e hc hz) hZ
      · rw [conj_pow,show c^3=1 from hco ▸ pow_orderOf_eq_one c,mul_one,mul_inv_cancel]
      · rw [inv_pow,show c^3=1 from hco ▸ pow_orderOf_eq_one c,inv_one]
      · have hi:quaternionInverter⁻¹=quaternionInverter:=
          inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using quaternionInverter_square)
        simpa only [map_mul,map_inv,hfc,hfv,inv_inv,hi] using quaternionInverter_inverts
end WreathedVertex
