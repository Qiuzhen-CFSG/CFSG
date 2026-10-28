module
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
/-!
# The actual residual still induces the entire chosen-module action

The source cover L=L_A O2(L) and centralization of V by O2(L) make the
restricted action of L_A surjective onto Aut_L(V). The faithful action-kernel
bound places its literal kernel in a two-group. The theorem records the
original conjugation formula as well as surjectivity and the kernel property.

Source: Aschbacher--Smith 4.4.5--10, printed pp.620--621, specialized to the
original chosen module. This prepares the G2(2)' simple-section outer test.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section04
open ChapterE
variable {G:Type*} [Group G] [Finite G]
/-- Restriction to the actual fixed residual preserves the original action quotient and two-group kernel. -/
theorem chosen_oddActorResidual_action_surjective
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G)) :
    ∃q:oddActorResidual L A→*inducedAutomizer V L,
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∀f:oddActorResidual L A,(q f).val.val=
        V.normalizerMonoidHom ⟨f.val,D.normalizes ((oddActorResidual_le L A).trans inf_le_left f.property)⟩ := by
  let F:=oddActorResidual L A
  have hFL:F≤L:=(oddActorResidual_le L A).trans inf_le_left
  have hFN:F≤normalizer (V:Set G):=hFL.trans D.normalizes
  let r:=V.normalizerMonoidHom.rangeRestrict
  let a:F→*Automizer V:=r.comp (inclusion hFN)
  let q:F→*inducedAutomizer V L:=a.codRestrict _ (fun f=>
    mem_map_of_mem r (show (⟨f.val,hFN f.property⟩:normalizer (V:Set G))∈L.subgroupOf _ from hFL f.property))
  have hQLT:L.pCoreIn 2≤(L⊔(T:Subgroup G)).pCoreIn 2:=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hQV:L.pCoreIn 2≤centralizer (V:Set G):=hQLT.trans D.core_centralizes
  have hq:Function.Surjective q:=by
    intro y
    obtain ⟨l,hl,he⟩:=y.property
    obtain ⟨hc,_,_,_⟩:=chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
    have hlc:(l:G)∈(F:Set G)*(L.pCoreIn 2:Set G):=hc ▸ hl
    obtain ⟨f,hf,c,hc,hfc⟩:=hlc
    let fn:normalizer (V:Set G):=⟨f,hFN hf⟩
    let cn:normalizer (V:Set G):=⟨c,Subgroup.centralizer_le_normalizer _ (hQV hc)⟩
    have hc1:r cn=1:=by
      apply Subtype.ext
      change V.normalizerMonoidHom cn=1
      rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
      exact hQV hc
    refine ⟨⟨f,hf⟩,?_⟩
    apply Subtype.ext
    change r fn=y.val
    rw [←he,show l=fn*cn from Subtype.ext hfc.symm,map_mul,hc1,mul_one]
  have hk:q.ker≤(L.pCoreIn 2).comap F.subtype:=by
    intro f hf
    have hh:r (inclusion hFN f)=1:=congrArg Subtype.val hf
    have hh':V.normalizerMonoidHom (inclusion hFN f)=1:=congrArg Subtype.val hh
    have hc:(f:G)∈centralizer (V:Set G):=by
      have hk':inclusion hFN f∈V.normalizerMonoidHom.ker:=hh'
      rw [normalizerMonoidHom_ker] at hk'
      exact hk'
    exact hfaith ⟨hFL f.property,hc⟩
  exact ⟨q,hq,((isPGroup_pCoreIn 2 L).comap_subtype).to_le hk,fun _=>rfl⟩
end CFSG.Quasithin.Chapter4.Section04
