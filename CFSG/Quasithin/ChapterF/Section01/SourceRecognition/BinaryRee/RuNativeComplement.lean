module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuExtensionObstruction

/-!
# The two native complement actors in the original first endpoint

The actual generated order-4096 extension is compared with the intrinsic
second core supplied by the other endpoint. Its bad census variants are
therefore excluded. The remaining standard actor is corrected by the
original five-element and fixed cyclic root, inside F₁ itself. Its action
is exactly the prescribed native order-four automorphism; the native
five-action and the original central marking are preserved.

Source: Aschbacher–Smith J.4.5, printed pp.441–442, and the verified
Shinoda complement action used in the binary Ree branch of F.1.12.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- Literal native five and four complement actors inside the original F₁. -/
theorem SourceChoice.exists_F₁_native_complement (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(e:fiveHyperplane d B5≃*ReeTwo.Core)(c b:p.F₁ B5),
      zpowers (e.symm (ReeTwo.Core.root 9):G)=d.toTypeRuSetup.Z ∧
      zpowers (c:G)=B5Image B5 ∧ orderOf c=5 ∧ b^4=1 ∧ b*c*b⁻¹=c^2 ∧
      (∀q:ReeTwo.Core,(e.symm (ReeTwo.Core.c q):G)=(c:G)*(e.symm q:G)*(c:G)⁻¹) ∧
      (∀q:ReeTwo.Core,(e.symm (ReeTwo.Core.a q):G)=(b:G)*(e.symm q:G)*(b:G)⁻¹) := by
  obtain ⟨e,c,g,hz,ht,hc,hco,ha,hgF,_hgB,hgSq,hsq,_hfour,hgfour,_hnot,hcard⟩:=
    s.exists_firstCore_extension_actor B5 hi
  let R:=fiveHyperplane d B5
  let S:=R⊔zpowers (g:G)
  have hRS:R≤S:=le_sup_left
  have hSF:S≤p.F₁ B5:=sup_le (p.fiveHyperplane_le_F₁ B5) (zpowers_le.mpr hgF)
  let j:ReeTwo.Core→*S:=(inclusion hRS).comp e.symm.toMonoidHom
  let aS:S:=⟨g,(show zpowers (g:G)≤S from le_sup_right) (mem_zpowers _)⟩
  let β:=firstCoreAction B5 e g
  have hj:j.range=R.subgroupOf S:=by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,inclusion_range]
  have hgen:j.range⊔zpowers aS=⊤:=by
    rw [hj]
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRS,MonoidHom.map_zpowers,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hconj:∀q,aS*j q*aS⁻¹=j (β q):=by
    intro q
    apply Subtype.ext
    have hh:=firstCoreAction_apply B5 e g (e.symm q)
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  have hfourS:aS^4=1 ∨ aS^4=j (ReeTwo.Core.root 9):=by
    rcases hgfour with h | h
    · exact Or.inl (Subtype.ext (by simpa only [coe_pow,coe_one] using h))
    · right
      apply Subtype.ext
      simpa only [coe_pow,aS,j,MonoidHom.comp_apply,coe_inclusion,MulEquiv.coe_toMonoidHom] using h
  obtain ⟨hfour,hroot,i,hstd,hβ⟩:=s.firstCore_extension_standard B5 hi S hSF hcard
    j aS β hz hgen hsq hconj hfourS
  let F:=p.F₁ B5
  have hFN:=s.F₁_normalizes_fiveHyperplane p B5 hi
  let f:F→*MulAut ReeTwo.Core:=(firstCoreAction B5 e).comp (inclusion hFN)
  let cF:F:=⟨c,(show B5Image B5≤F from le_sup_right) c.property⟩
  let aF:F:=⟨g,hgF⟩
  let tR:R:=e.symm (ReeTwo.Core.root 2)
  let tF:F:=inclusion (p.fiveHyperplane_le_F₁ B5) tR
  have ha4:aF^4=1:=Subtype.ext (by
    have hh:=congrArg (fun x:S=>(x:G)) hfour
    simpa only [coe_pow,coe_one] using hh)
  have ht4:tF^4=1:=by
    change inclusion (p.fiveHyperplane_le_F₁ B5) tR^4=1
    rw [←map_pow,firstCore_fourth_power,map_one]
  have hac:aF*cF*aF⁻¹=cF^2:=Subtype.ext (hgSq c c.property)
  have hct:Commute cF tF:=Subtype.ext (ht c c.property)
  have hat:Commute aF tF:=by
    apply Subtype.ext
    apply mul_inv_eq_iff_eq_mul.mp
    have hh:=firstCoreAction_apply B5 e g tR
    rw [show e tR=ReeTwo.Core.root 2 from e.apply_symm_apply _,hroot] at hh
    exact hh.symm
  have hfc:f cF=ReeTwo.Core.c:=by
    apply MulEquiv.ext
    intro q
    apply e.symm.injective
    apply Subtype.ext
    have hh:=firstCoreAction_apply B5 e (inclusion hFN cF) (e.symm q)
    rw [e.apply_symm_apply] at hh
    exact hh.trans (ha q).symm
  have hft:f tF=MulAut.conj (ReeTwo.Core.root 2):=by
    apply MulEquiv.ext
    intro q
    change e (tR*e.symm q*tR⁻¹)=ReeTwo.Core.root 2*q*(ReeTwo.Core.root 2)⁻¹
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply,e.apply_symm_apply]
  have hfa:f aF=ReeTwo.Core.FixingActionCensus.representative i:=hβ
  obtain ⟨b,hb4,hbc,hfb⟩:=ReeTwo.Core.FixingActionCensus.exists_standard_actor
    f cF aF tF ha4 ht4 hac hct hat hfc hft i hstd hfa
  have hcF:orderOf cF=5:=by
    rw [←orderOf_coe cF]
    exact (orderOf_coe c).trans hco
  refine ⟨e,cF,b,hz,hc,hcF,hb4,hbc,ha,?_⟩
  intro q
  have hh:=firstCoreAction_apply B5 e (inclusion hFN b) (e.symm q)
  rw [e.apply_symm_apply] at hh
  change (e.symm (f b q):G)=(b:G)*(e.symm q:G)*(b:G)⁻¹ at hh
  rw [hfb] at hh
  exact hh

end CFSG.Quasithin.ChapterJ.RuSubgroup
