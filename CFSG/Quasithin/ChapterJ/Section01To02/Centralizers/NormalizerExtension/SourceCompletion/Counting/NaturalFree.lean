module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.Suzuki
public import Theory.Representation.BinaryConjugationSection.InvariantCount
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer

/-!
# Freeness of the source natural sections for even involutions

A nontrivial involution in the marked A5 acts nontrivially on its natural
four-space. Its displacement range is contained in its kernel. The existing
no-transvection theorem excludes rank one, so both spaces have dimension two
and agree. The actual source action therefore satisfies the freeness identity
needed for the two four-fold fiber counts in J.2.7(8).
-/

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ

public theorem natural_free_involution (r:L2FourAction) (t:S5) (ht:t^2=1) (ht1:t≠1)
    (he:t∈alternatingGroup (Fin 5)) : Fusion.Outer.FreeAt r.action t := by
  let a:=r.action t
  have ha2 : a*a=1 := by rw [←map_mul,←pow_two,ht,map_one]
  have ha1 : a≠1 := by
    intro ha
    let g:=r.marking.symm ⟨t,he⟩
    have hg : SL2FourNatural.action g=1 := by
      apply LinearEquiv.ext
      intro v
      rw [←r.restriction]
      change r.action ((r.marking (r.marking.symm ⟨t,he⟩)):S5) v=v
      rw [r.marking.apply_symm_apply]
      exact LinearMap.congr_fun ha v
    have hg1 : g=1 := SL2FourNatural.action_faithful (hg.trans (map_one _).symm)
    have hh := congrArg (fun x => ((r.marking x):S5)) hg1
    exact ht1 (by simpa only [g,r.marking.apply_symm_apply,map_one,Subgroup.coe_one] using hh)
  let D:=a-1
  have hincl : D.range≤D.ker := by
    rintro _ ⟨w,rfl⟩
    change a (a w-w)-(a w-w)=0
    have haa : a (a w)=w := LinearMap.congr_fun ha2 w
    rw [map_sub,haa]
    have hww : w+w=0 := ZModModule.add_self w
    have haw : a w+a w=0 := ZModModule.add_self (a w)
    calc
      w-a w-(a w-w)=(w+w)-(a w+a w) := by abel
      _=0 := by rw [hww,haw,sub_self]
  have hdim:=D.finrank_range_add_finrank_ker
  rw [SL2FourNatural.finrank_vector] at hdim
  have hr0 : Module.finrank (ZMod 2) D.range≠0 := by
    intro h
    exact ha1 (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)))
  have hr1 : Module.finrank (ZMod 2) D.range≠1 := r.no_rank_one t
  have hEq : D.range=D.ker := Submodule.eq_of_le_of_finrank_eq hincl
    (by have := Submodule.finrank_mono hincl;omega)
  intro v hv
  have hvk : v∈D.ker := by change a v-v=0;rw [hv,sub_self]
  obtain ⟨w,hw⟩ := hEq.symm ▸ hvk
  refine ⟨w,?_⟩
  change a w-w=v at hw
  simpa only [sub_eq_add_neg,neg_eq_of_add_eq_zero_left (ZModModule.add_self w)] using hw

end CFSG.Quasithin.ChapterJ
