module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.CoreModel
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The actual nonabelian core of an order-96 wreathed vertex

An element of order three induces a nontrivial cubic automorphism on a normal
self-centralizing two-group: its conjugation kernel is again a two-group.
Place the unchanged core inside the supplied Sylow subgroup and transport its
centricity through the exact wreath equivalence. The ABG core classification
then yields the quaternion–cyclic model on the original two-core.

This proves the core-identification step in the order-96 nonabelian vertex of
Aschbacher–Smith F.1.12(I)(8). No core-model premise is retained in the source
consumer `twoCore_equiv_of_card96`.
-/

public section
noncomputable section
open Subgroup
namespace WreathedVertex
variable {G:Type*} [Group G] [Finite G]

theorem core_aut_not_two (Q:Subgroup G) [Q.Normal] (hQ:IsPGroup 2 Q)
    (hc:centralizer (Q:Set G)≤Q) (h3:3∣Nat.card G) : ¬IsPGroup 2 (MulAut Q) := by
  let f:G→*MulAut Q:=MulAut.conjNormal
  have hk:f.ker≤Q := by
    intro g hg
    apply hc
    intro a ha
    have hh:=DFunLike.congr_fun (show f g=1 from hg) (⟨a,ha⟩:Q)
    have hv:=congrArg (fun q:Q=>(q:G)) hh
    change g*a*g⁻¹=a at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have hker:IsPGroup 2 f.ker:=hQ.of_injective (inclusion hk) (inclusion_injective hk)
  obtain ⟨c,hc3⟩:=exists_prime_orderOf_dvd_card' (G:=G) 3 h3
  have hfc:orderOf (f c)=3:=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hker c (by rw [hc3];decide)).trans hc3
  intro hp
  have hn:f c≠1 := by intro he;rw [he,orderOf_one] at hfc;omega
  have hh:=hp.dvd_orderOf hn
  rw [hfc] at hh
  norm_num at hh

theorem core_equiv (Q:Subgroup G) [Q.Normal] (hQ:IsPGroup 2 Q)
    (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q) (h3:3∣Nat.card G)
    (S:Sylow 2 G) (eS:S≃*W) : Nonempty (Q≃*QuaternionCyclic.Model) := by
  have hQS:Q≤S:=hQ.le_sylow_of_normal S
  let K:Subgroup S:=Q.subgroupOf S
  let X:Subgroup W:=K.map eS.toMonoidHom
  let eK:K≃*Q:=subgroupOfEquivOfLe hQS
  let eX:K≃*X:=K.equivMapOfInjective eS.toMonoidHom eS.injective
  let e:Q≃*X:=eK.symm.trans eX
  have hcent:centralizer (X:Set W)≤X := by
    intro x hx
    have hs:(eS.symm x:G)∈Q := by
      apply hc
      intro a ha
      let aS:S:=⟨a,hQS ha⟩
      have haX:eS aS∈X:=⟨aS,ha,rfl⟩
      have hh:=hx _ haX
      have he: aS*eS.symm x=eS.symm x*aS := by
        apply eS.injective
        simpa only [map_mul,eS.apply_symm_apply] using hh
      exact congrArg (fun a:S=>(a:G)) he
    exact ⟨eS.symm x,hs,eS.apply_symm_apply x⟩
  have hn:¬IsMulCommutative X := by
    intro hh
    apply hna
    exact IsMulCommutative.of_comm (fun a b=>e.injective (by
      rw [map_mul,map_mul];exact hh.is_comm.comm _ _))
  have ha:¬IsPGroup 2 (MulAut X) := by
    intro hh
    exact core_aut_not_two Q hQ hc h3 (hh.of_equiv (MulAut.congr e).symm)
  obtain ⟨f⟩:=nonabelian_centric_model X hcent hn ha
  exact ⟨e.trans f⟩

theorem twoCore_equiv_of_card96 (hG:Nat.card G=96)
    (hc:centralizer (pCore 2 G:Set G)≤pCore 2 G) (hna:¬IsMulCommutative (pCore 2 G))
    (S:Sylow 2 G) (eS:S≃*W) : Nonempty (pCore 2 G≃*QuaternionCyclic.Model) :=
  core_equiv (pCore 2 G) (pCore_isPGroup (p:=2) (G:=G)) hc hna (by rw [hG];decide) S eS

end WreathedVertex
