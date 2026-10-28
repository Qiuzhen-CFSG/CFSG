module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.MatchingParabolics
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.Centered

/-!
# Excluding the Ree component with the original centered module

The matched Suzuki configuration supplies relative normality of the actual
residual image in the full Ree parabolic. Restricting the component's
central quotient, including its conjugation, gives a central-kernel map
from the original perfect residual. The parabolic centered-module theorem
then contradicts the original nontrivial commutator module.
Source: Aschbacher--Smith 4.4.12, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

/-- The actual full-parabolic representation of the residual excludes the
Ree component. No abstract family comparison replaces its central cover. -/
theorem no_ree_suzuki_centered_residual
    {G S : Type*} [Group G] [Finite G] [Group S]
    {L A W : Subgroup G}
    (hWF : W ≤ (oddActorResidual L A).pCoreIn 2) (hne : W ≠ ⊥)
    (hcomm : W = ⁅W,oddActorResidual L A⁆)
    (hcent : W ≤ centralizer ((oddActorResidual L A).pCoreIn 2 : Set G))
    (hn : ¬ Group.IsSolvable (oddActorResidual L A))
    (hc : ReeSuzukiComponentCase L W A S) : False := by
  obtain ⟨K,_,_,_,_,_,hFK,_,_,_,m,hm,e,g,hg,_,hnorm⟩ := hc
  let J := K.map (normalizer (A : Set G)).subtype
  let q := (MulAut.conj g).toMonoidHom.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (center J)))
  let P := ReeF4.ConverseParabolics.parabolic m .suzuki
  let v := q.comp (inclusion hFK)
  have hv : v.range ≤ P := by
    simpa only [v,q,residualQuotientMap,MonoidHom.comp_assoc,MonoidHom.range_comp] using hg
  have hk : q.ker ≤ center J := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    apply (MulAut.conj g).injective
    exact hx.trans (by simp only [map_one])
  let f := v.codRestrict P (fun x => hv ⟨x,rfl⟩)
  have hfRange : f.range = v.range.subgroupOf P := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  let : f.range.Normal := hfRange.symm ▸ hnorm
  let F := oddActorResidual L A
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  have hfker : f.ker ≤ center F := by
    intro x hx
    have hxk : inclusion hFK x ∈ center J := hk (congrArg Subtype.val hx)
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg J.subtype (mem_center_iff.mp hxk (inclusion hFK y)))
  have hWF' : W ≤ F := hWF.trans (pCoreIn_le 2 F)
  have hWc : W.subgroupOf F ≤ centralizer (pCore 2 F : Set F) := by
    intro w hw x hx
    exact Subtype.ext (hcent hw _ (mem_map_of_mem F.subtype hx))
  have he : W.subgroupOf F = ⁅W.subgroupOf F,⊤⁆ := by
    apply map_injective F.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWF',← MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  have hb := ReeF4.ConverseParabolics.CoreActionRigidity.suzuki_no_centered_commutator
    hm hn f hfker (W.subgroupOf F) hWc he
  apply hne
  have hz := congrArg (map F.subtype) hb
  simpa only [map_subgroupOf_eq_of_le hWF',Subgroup.map_bot] using hz
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
