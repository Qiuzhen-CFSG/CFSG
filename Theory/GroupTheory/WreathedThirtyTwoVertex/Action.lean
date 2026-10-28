module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.CoreCenter
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicAutomorphisms
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# The full quaternion action of the wreathed vertex

The core center is central in the vertex. Restrict conjugation to the intrinsic quaternion factor. Its kernel is the same center of order four; the image therefore has order24 and fills Aut(Q8). This constructs the actual source action used to lift the cubic and its inverter.

Source: Aschbacher–Smith F.1.12(I)(8), the nonabelian order-96 vertex.
-/

@[expose] public section

noncomputable section
open Subgroup
namespace WreathedVertex
variable {G:Type*} [Group G]

def coreAction (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model) :
    G→*MulAut QuaternionCyclic.Model :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

def quaternionAction (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model) :
    G→*MulAut (QuaternionGroup 2) := QuaternionCyclic.restrictionHom.comp (coreAction Q e)

theorem coreAction_fixes_center (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model)
    (hz:(center Q).map Q.subtype≤center G) (g:G) :
    coreAction Q e g QuaternionCyclic.r=QuaternionCyclic.r := by
  have hr:QuaternionCyclic.r∈center QuaternionCyclic.Model := by
    rw [QuaternionCyclic.center_eq_cyclic]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hh:(e.symm QuaternionCyclic.r:G)∈center G :=
    hz ⟨e.symm QuaternionCyclic.r,(centerCongr e.symm ⟨_,hr⟩).property,rfl⟩
  change e (MulAut.conjNormal g (e.symm QuaternionCyclic.r))=QuaternionCyclic.r
  apply (e.toEquiv.eq_symm_apply).mp
  apply Subtype.ext
  change g*(e.symm QuaternionCyclic.r:G)*g⁻¹=(e.symm QuaternionCyclic.r:G)
  rw [mem_center_iff.mp hh g,mul_inv_cancel_right]

theorem coreAction_eq_extension (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model)
    (hz:(center Q).map Q.subtype≤center G) (g:G) :
    coreAction Q e g=QuaternionCyclic.extendAutHom (quaternionAction Q e g) := by
  symm
  exact QuaternionCyclic.extend_restriction_of_sign_one _
    ((QuaternionCyclic.centralSign_eq_one_iff _).mpr (coreAction_fixes_center Q e hz g))

theorem quaternionAction_ker (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model)
    (hc:centralizer (Q:Set G)≤Q) (hz:(center Q).map Q.subtype≤center G) :
    (quaternionAction Q e).ker=center G := by
  ext g
  constructor
  · intro hg
    have hf:coreAction Q e g=1 := by
      rw [coreAction_eq_extension Q e hz g,show quaternionAction Q e g=1 from hg,map_one]
    have hgC:g∈centralizer (Q:Set G) := by
      intro a ha
      have he:=DFunLike.congr_fun hf (e ⟨a,ha⟩)
      have he':MulAut.conjNormal g (⟨a,ha⟩:Q)=⟨a,ha⟩ := by
        apply e.injective
        simpa only [coreAction,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
          MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,
          MulAut.one_apply] using he
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg (fun a:Q=>(a:G)) he')).symm
    have hgQ:=hc hgC
    exact hz ⟨⟨g,hgQ⟩,mem_center_iff.mpr (fun a=>Subtype.ext (hgC a a.property)),rfl⟩
  · intro hg
    change QuaternionCyclic.restrictionHom (coreAction Q e g)=1
    have hf:coreAction Q e g=1 := by
      apply MulEquiv.ext
      intro a
      change e (MulAut.conjNormal g (e.symm a))=a
      have he:MulAut.conjNormal g (e.symm a)=e.symm a := by
        apply Subtype.ext
        change g*(e.symm a:G)*g⁻¹=(e.symm a:G)
        rw [←mem_center_iff.mp hg (e.symm a),mul_inv_cancel_right]
      rw [he,e.apply_symm_apply]
    rw [hf,map_one]

theorem quaternionAction_surjective [Finite G] (Q:Subgroup G) [Q.Normal]
    (e:Q≃*QuaternionCyclic.Model) (hG:Nat.card G=96)
    (hc:centralizer (Q:Set G)≤Q) (hz:(center Q).map Q.subtype≤center G)
    (hZ:Nat.card (center G)=4) : Function.Surjective (quaternionAction Q e) := by
  let f:=quaternionAction Q e
  have hk:Nat.card f.ker=4 := by rw [quaternionAction_ker Q e hc hz,hZ]
  have hr:Nat.card f.range=24 := by
    have hh:=f.ker.card_mul_index
    rw [index_ker,hk,hG] at hh
    omega
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  exact hr.trans QuaternionGroup.card_mulAut_two.symm
end WreathedVertex
