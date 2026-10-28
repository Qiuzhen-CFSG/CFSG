module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Centralizer

/-!
# The A₆ centralizer equality from original source data

The actual normal source component and compatible surjective H-action supply
all earlier inputs of the proved 2.5.22 centralizer argument. The 2.5.18
source results give normality in G_t, its centralizer supplement and
characteristic two. An outside Sylow-normalizer element is selected internally;
its actual action transports the disjoint two-core conjugate to the kernel
in the original Sylow of G_t.

The result proves H = C_G(t), retaining only the genuine independent
2.5.20 normality and 2.5.21 surjective Aut(A₆) action conclusions. No later
Frattini, fusion or terminal source assertion is used.

Source: Aschbacher--Smith, 2.5.18, p.560, and 2.5.22(2), printed p.567.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow
open ComponentRefinement Section05.ComponentSelection Section05.Overcomponents
variable {G:Type*} [Group G] [Finite G] {H K M:Subgroup G} {S:Sylow 2 H} {z:G}

/-- The original A₆ source centralizer equality. The complete 2.5.18 inputs and
crossing kernel are constructed; only the actual 2.5.20 normality and 2.5.21
surjective component action remain as genuine earlier source conclusions. -/
theorem centralizer_eq_of_original_source
    (c:MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    (hstar:H∈gammaStar (Chapter1.He G) M)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype))
    (eK:K≃*alternatingGroup (Fin 6))
    (f:H→*AlternatingSix.ShadowLocal.AutA6) (hf:Function.Surjective f)
    (hcompat:∀(h:H)(k:K),(eK.symm (f h (eK k)):G)=(h:G)*(k:G)*(h:G)⁻¹) :
    H=centralizer ({t}:Set G) := by
  let J:=centralizer ({t}:Set G)
  let Y:=(S:Subgroup H).map H.subtype
  obtain ⟨hHJ,_,⟨P,hP⟩,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKJ:K≤J:=c.component_le.trans hHJ
  let B:=K.subgroupOf J
  let : B.Normal:=(normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ)
  let eB:B≃*alternatingGroup (Fin 6):=(subgroupOfEquivOfLe hKJ).trans eK
  have hchar:centralizer (pCore 2 (centralizer (B:Set J)):Set (centralizer (B:Set J)))≤
      pCore 2 (centralizer (B:Set J)):=by
    let e:centralizer (B:Set J)≃*(J⊓centralizer (K:Set G):Subgroup G):={
      toFun x:=⟨x.val.val,x.val.property,fun k hk=>congrArg Subtype.val (x.property ⟨k,hKJ hk⟩ hk)⟩
      invFun x:=⟨⟨x.val,x.property.1⟩,fun k hk=>Subtype.ext (x.property.2 k.val hk)⟩
      left_inv _:=rfl
      right_inv _:=rfl
      map_mul' _ _:=rfl }
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      (Chapter1.mem_He_iff.mp (source_normal_component_centralizer_mem_He
        c hG hempty hgen hb hstar t ht htC htZ).2)
  have hsurj:Function.Surjective (AlternatingSix.ShadowLocal.conjugationAction B eB):=by
    intro a
    obtain ⟨h,rfl⟩:=hf a
    refine ⟨⟨h,hHJ h.property⟩,?_⟩
    apply MulEquiv.ext
    intro v
    obtain ⟨b,rfl⟩:=eB.surjective v
    rw [AlternatingSix.ShadowLocal.conjugationAction_apply]
    apply eK.symm.injective
    apply Subtype.ext
    simp only [eB,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    exact (congrArg Subtype.val (MulAut.conjNormal_apply (⟨h,hHJ h.property⟩:J) b)).trans
      (hcompat h ((subgroupOfEquivOfLe hKJ) b)).symm
  have hgenJ:B⊔(P:Subgroup J)⊔centralizer (B:Set J)=⊤:=by
    apply (Subgroup.map_injective J.subtype_injective)
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.map_centralizer_subtype,
      map_subgroupOf_eq_of_le hKJ,hP,←MonoidHom.range_eq_map,range_subtype]
    rw [←hgen]
    exact (source_normal_component_centralizer_supplement c hG hempty hgen hb hstar t ht htC htZ).symm
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem Y (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  have hcross:Disjoint (twoCore H) ((twoCore H).conjBy x⁻¹):=
    (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  let ep:P≃*Y:=((P:Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hP)
  let ay:MulAut Y:=Y.normalizerMonoidHom ⟨x⁻¹,(normalizer (Y:Set G)).inv_mem hxN⟩
  let a:MulAut P:=MulAut.congr ep.symm ay
  let inc:P→*G:=J.subtype.comp (P:Subgroup J).subtype
  have hinc:Function.Injective inc:=J.subtype_injective.comp (P:Subgroup J).subtype_injective
  have ha (p:P):inc (a p)=x⁻¹*inc p*x:=by
    have he:ep (a p)=ay (ep p):=by simp only [a,MulAut.congr_apply,MulEquiv.symm_symm,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    have hh:=congrArg (fun y:Y=>(y:G)) he
    change inc (a p)=x⁻¹*inc p*(x⁻¹)⁻¹ at hh
    simpa only [inv_inv] using hh
  have hD (p:P) (hp:p∈(centralizer (B:Set J)).subgroupOf P):inc p∈twoCore H:=by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    refine ⟨hP ▸ mem_map_of_mem J.subtype p.property,?_⟩
    intro k hk
    exact congrArg Subtype.val (hp ⟨k,hKJ hk⟩ hk)
  have hd:Disjoint ((centralizer (B:Set J)).subgroupOf P)
      (((centralizer (B:Set J)).subgroupOf P).map a.toMonoidHom):=by
    apply disjoint_iff_inf_le.mpr
    rintro p ⟨hp,⟨q,hq,rfl⟩⟩
    have hqC:=hD q hq
    have haC:=hD (a q) hp
    have hqX:inc (a q)∈(twoCore H).conjBy x⁻¹:=by
      rw [ha]
      exact ⟨inc q,hqC,by change x⁻¹*inc q*(x⁻¹)⁻¹=x⁻¹*inc q*x; rw [inv_inv]⟩
    have he:inc (a q)=1:=mem_bot.mp ((disjoint_iff_inf_le.mp hcross) ⟨haC,hqX⟩)
    exact hinc (he.trans inc.map_one.symm)
  apply CFSG.Quasithin.Chapter2.A6Shadow.centralizer_eq_of_earlier_source hG t ht H B eB P
    ?_ hgenJ hchar hsurj a hd
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKJ,hP,←hgen]

end CFSG.Quasithin.Chapter2.A6Shadow
