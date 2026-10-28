module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.NativeActors
public import Theory.GroupTheory.CubicCentralSquareExtension.Generation
/-!
# A unique whole vertex over the nonabelian wreathed core

Construct the quaternion–cyclic coordinates and both marked actors from the
original two-core. Their images generate the quotient of order six, so the
core and actors generate the whole vertex. The fixed central-square
presentation then compares any two such order-96 groups without retaining
an action, splitting or model-identification premise.

Source: Aschbacher–Smith F.1.12(I)(8), the nonabelian G₂(2)′ endpoint.
-/
@[expose] public section

noncomputable section
open Subgroup
namespace WreathedVertex
variable {G:Type*} [Group G] [Finite G]

def modelInclusion (Q:Subgroup G) (e:Q≃*QuaternionCyclic.Model) :
    QuaternionCyclic.Model→*G := Q.subtype.comp e.symm.toMonoidHom

omit [Finite G] in
theorem modelInclusion_range (Q:Subgroup G) (e:Q≃*QuaternionCyclic.Model) :
    (modelInclusion Q e).range=Q := by
  ext g
  constructor
  · rintro ⟨a,rfl⟩
    exact (e.symm a).property
  · intro hg
    exact ⟨e ⟨g,hg⟩,by change (e.symm (e ⟨g,hg⟩):G)=g;rw [e.symm_apply_apply]⟩

omit [Finite G] in
theorem modelInclusion_action (Q:Subgroup G) [Q.Normal] (e:Q≃*QuaternionCyclic.Model)
    (hz:(center Q).map Q.subtype≤center G) (g:G) (α:MulAut (QuaternionGroup 2))
    (hg:quaternionAction Q e g=α) (a:QuaternionCyclic.Model) :
    modelInclusion Q e (QuaternionCyclic.extendAutHom α a)=
      g*modelInclusion Q e a*g⁻¹ := by
  have hh:=coreAction_eq_extension Q e hz g
  rw [hg] at hh
  have he:=congrArg e.symm (DFunLike.congr_fun hh a)
  change e.symm (e (MulAut.conjNormal g (e.symm a)))=e.symm (QuaternionCyclic.extendAutHom α a) at he
  rw [e.symm_apply_apply] at he
  exact (congrArg (fun x:Q=>(x:G)) he).symm

theorem exists_native_presentation (hG:Nat.card G=96)
    (hc:centralizer (pCore 2 G:Set G)≤pCore 2 G) (hna:¬IsMulCommutative (pCore 2 G))
    (S:Sylow 2 G) (eS:S≃*W) :
    ∃(e:pCore 2 G≃*QuaternionCyclic.Model) (c v:G),
      CubicCentralSquareExtension.Relations (modelInclusion (pCore 2 G) e) c v
        QuaternionCyclic.cubic (QuaternionCyclic.extendAutHom quaternionInverter) QuaternionCyclic.r∧
      CubicCentralSquareExtension.generated (modelInclusion (pCore 2 G) e) c v=⊤ := by
  let Q:=pCore 2 G
  have hQ:IsPGroup 2 Q:=pCore_isPGroup (p:=2) (G:=G)
  obtain ⟨e⟩:=twoCore_equiv_of_card96 hG hc hna S eS
  obtain ⟨c,v,hco,hfc,hfv,hv,hvc⟩:=native_actors Q hQ hc hna hG S eS e
  have hz:=core_center_central Q hQ hc hna (by rw [hG];decide) S eS
  have h6:Nat.card (G⧸Q)=6 := by
    have hh:=Q.card_mul_index
    have hcard:Nat.card Q=16:=(Nat.card_congr e.toEquiv).trans QuaternionCyclic.card_model
    rw [hcard,hG] at hh
    change Q.index=6
    omega
  refine ⟨e,c,v,?_,?_⟩
  · exact ⟨hco ▸ pow_orderOf_eq_one c,hv,hvc,
      modelInclusion_action Q e hz c _ hfc,modelInclusion_action Q e hz v _ hfv⟩
  · exact CubicCentralSquareExtension.generated_eq_top_of_six_quotient Q _ (modelInclusion_range Q e)
      c v hco (hv ▸ (e.symm QuaternionCyclic.r).property) hvc hQ h6

variable {H:Type*} [Group H] [Finite H]
theorem equiv_of_card96 (hG:Nat.card G=96) (hH:Nat.card H=96)
    (hcG:centralizer (pCore 2 G:Set G)≤pCore 2 G) (hcH:centralizer (pCore 2 H:Set H)≤pCore 2 H)
    (hnaG:¬IsMulCommutative (pCore 2 G)) (hnaH:¬IsMulCommutative (pCore 2 H))
    (S:Sylow 2 G) (T:Sylow 2 H) (eS:S≃*W) (eT:T≃*W) : Nonempty (G≃*H) := by
  obtain ⟨e,c,v,hrel,hgen⟩:=exists_native_presentation hG hcG hnaG S eS
  obtain ⟨f,d,t,hrel',hgen'⟩:=exists_native_presentation hH hcH hnaH T eT
  obtain ⟨E,_,_,_⟩:=CubicCentralSquareExtension.exists_equiv _ _ c v d t
    QuaternionCyclic.cubic (QuaternionCyclic.extendAutHom quaternionInverter) QuaternionCyclic.r
    hrel hrel' hgen hgen' (by rw [hG,QuaternionCyclic.card_model]) (by rw [hH,QuaternionCyclic.card_model])
  exact ⟨E⟩
end WreathedVertex
