module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusionSelection
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusionComplement
/-!
# The complement aligned with the original fusion witness

Generate A from K and the outer involution aˣ selected by the crossing.
Its actual action identifies A with Aut(PSL₃(3)), with K the literal
preimage of the inner subgroup. The action kernel ⟨t⟩ gives H=⟨t⟩×A.
This is the source replacement of the outer generator, made directly
from the involution needed by the ensuing fusion argument.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_fusion_split
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S:Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U≤(S:Subgroup H).map H.subtype)
    (eK : K≃*Matrix.PSL3Three.PSL) :
    z∈K ∧ ∃ t a x : G, orderOf t=2 ∧ centralizer ({t}:Set G)=H ∧ ¬IsConj t z ∧
      a∈K ∧ orderOf a=2 ∧ x⁻¹*t*x=t*z ∧
      ∃ A : Subgroup G, K≤A ∧ ∃ eA:A≃*MulAut Matrix.PSL3Three.PSL,
      K.subgroupOf A=(MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom ∧
      H=zpowers t⊔A ∧ Disjoint (zpowers t) A ∧ zpowers t≤centralizer (A:Set G) ∧
      ∃ f:A, (f:G)=x⁻¹*a*x ∧ (f:G)∉K := by
  obtain ⟨hzK,t,a,x,ht,htC,htZ,hcore,hCt,htz,haK,hao,htx,f,hfe,hfo,hfa⟩ :=
    linear_three_source_fusion_selection c hG hempty hgen hb hp hUS eK
  obtain ⟨hAH,hbij⟩ := linear_three_outer_involution_complement_equiv c eK f hfa hfo
  let A := K⊔zpowers (f:G)
  let α := MathieuSourceSetup.componentAction c
  let β : A →* MulAut K := α.comp (inclusion hAH)
  let eA : A≃*MulAut Matrix.PSL3Three.PSL :=
    (MulEquiv.ofBijective β hbij).trans (MulAut.congr eK)
  have hker : α.ker=(zpowers t).subgroupOf H := by
    rw [normal_component_source_action_ker c hG hempty hgen,hcore]
  have hdis : Disjoint (zpowers t) A := by
    apply disjoint_def.mpr
    intro b hbT hbA
    have hba : α ⟨b,hAH hbA⟩=1 := by
      change (⟨b,hAH hbA⟩:H)∈α.ker
      rw [hker]; exact hbT
    have hh : β ⟨b,hbA⟩=β 1 := by rw [map_one]; exact hba
    exact congrArg Subtype.val (hbij.1 hh)
  have hspan : H=zpowers t⊔A := by
    apply le_antisymm ?_ (sup_le (zpowers_le.mpr (pCoreIn_le 2 H htC)) hAH)
    intro b hbH
    obtain ⟨d,hd⟩ := hbij.2 (α ⟨b,hbH⟩)
    have hdker : (⟨b,hbH⟩:H)*(inclusion hAH d)⁻¹∈α.ker := by
      change α ((⟨b,hbH⟩:H)*(inclusion hAH d)⁻¹)=1
      rw [map_mul,map_inv,← hd]
      exact mul_inv_cancel _
    rw [hker] at hdker
    have hh := (zpowers t⊔A).mul_mem (mem_sup_left hdker) (mem_sup_right d.property)
    change b * (d:G)⁻¹ * (d:G) ∈ zpowers t⊔A at hh
    simpa only [inv_mul_cancel_right] using hh
  have hcomm : zpowers t≤centralizer (A:Set G) := by
    apply zpowers_le.mpr
    intro b hb
    exact (mem_centralizer_singleton_iff.mp (hCt.symm ▸ hAH hb))
  have hinner : K.subgroupOf A=(MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom := by
    ext b
    change (b:G)∈K ↔ MulAut.congr eK (β b)∈MulAut.innerSubgroup Matrix.PSL3Three.PSL
    rw [← MulAut.map_innerSubgroup_congr eK,mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
    constructor
    · intro hb
      refine ⟨⟨b,hb⟩,?_⟩
      ext r
      rfl
    · rintro ⟨k,hk⟩
      have hh : β (⟨k,mem_sup_left k.property⟩:A)=β b := by
        calc β (⟨k,mem_sup_left k.property⟩:A) = MulAut.conj k := by ext r; rfl
             _ = β b := hk
      have he := congrArg Subtype.val (hbij.1 hh)
      exact he ▸ k.property
  have hfK : (f:G)∉K := by
    intro hfK
    apply hfa
    refine ⟨⟨f,hfK⟩,?_⟩
    ext r
    rfl
  exact ⟨hzK,t,a,x,ht,hCt,htz,haK,hao,htx,A,le_sup_left,eA,hinner,hspan,hdis,hcomm,
    ⟨f,mem_sup_right (mem_zpowers (f:G))⟩,hfe,hfK⟩
end CFSG.Quasithin.Chapter2.Section05
