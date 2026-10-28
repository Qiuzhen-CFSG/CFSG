module
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram.LocalCore
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram.CoreImage
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic


/-!
# The nonabelian closure case of the exceptional diagram argument

The original source hypotheses produce the actual invariant two-core
Q containing O₂(Y). For the marked action of Mc on PSL₃(4), its two-core
acts trivially: every automorphism overgroup containing the inner group
has trivial two-core. The core image is therefore elementary, and the
nontrivial diagram action puts it inside the inner automorphisms.
The marked parabolic-normalizer containment then gives O₂(Y) ≤ S.

Only the preceding source12 action and its literal normalizer transport
remain as inputs. The core factorization, elementarity and inner placement
are proved here from the original ambient hypotheses.
Source: Aschbacher–Smith, Lemma 14.2.13, printed p.984.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem twoCore_le_kernel_of_inner_action
    {X : Type*} [Group X] [Finite X]
    (ρ : X →* MulAut Matrix.PSL3Four.PSL)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range) :
    pCore 2 X ≤ ρ.ker := by
  have hc : center Matrix.PSL3Four.PSL = ⊥ := by
    let := Atlas.sl_perfect (F := Matrix.PSL3Four.F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot Matrix.PSL3Four.SL
  have hp : pCore 2 Matrix.PSL3Four.PSL = ⊥ := by
    exact bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  have hb : pCore 2 ρ.range = ⊥ := automorphism_core_eq_bot 2
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hc) hp ρ.range
    (fun x => hinner ⟨x,rfl⟩)
  have hn : ((pCore 2 X).map ρ.rangeRestrict).Normal :=
    (inferInstance : (pCore 2 X).Normal).map ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hm : (pCore 2 X).map ρ.rangeRestrict ≤ pCore 2 ρ.range :=
    le_sSup ⟨hn,pCore_isPGroup.map ρ.rangeRestrict⟩
  intro x hx
  have he : ρ.rangeRestrict x = 1 := (hb ▸ hm) (mem_map_of_mem ρ.rangeRestrict hx)
  exact congrArg Subtype.val he

/-- The exceptional nonabelian paragraph on the original Mc action and marked
parabolic residual. Earlier source12 supplies the action and its inner-action
normalizer containment; all source13 core and image facts are derived here. -/
theorem source_nonabelian_twoCore_le_of_marked_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hTMc : (T : Subgroup G) ≤ Mc)
    (ρ : Mc →* MulAut Matrix.PSL3Four.PSL)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range)
    (hswap : ∃ t ∈ ((T.subtype hTMc : Sylow 2 Mc) : Subgroup Mc),
      Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
        (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (ρ t) ≠ 1)
    (K₁ : Subgroup G)
    (hplace : (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap ρ).map Mc.subtype ≤
      (T : Subgroup G) ⊓ normalizer (K₁ : Set G)) :
    (sourceResidual M Mc).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K₁ : Set G) := by
  obtain ⟨he,F,g,hFH,_hU,hUc,hgP,_hgH,hbounds,hYQ,hQT,hnorm,hsplit⟩ :=
    source_nonabelian_core_geometry hG T hempty hM hu hmany hcard e hne
  let := he
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hHJ : F.H ≤ Mc := le_of_eq hFH
  have hkillU : F.U.subgroupOf Mc ≤ ρ.ker := by
    intro u hu
    obtain ⟨w,hw,heq⟩ := hUc hu
    have he : w = u := Subtype.ext heq
    exact he ▸ twoCore_le_kernel_of_inner_action ρ hinner hw
  have hQI := core_image_le_inner_in_overgroup F (sourceResidual M Mc)
    h.L_normalizes_seed g hgP hsplit hbounds.2 hQT hnorm Mc hHJ ρ hkillU hinner hswap
  intro x hx
  have hxQ := hYQ hx
  have hxT := hQT hxQ
  have hxMc := hTMc hxT
  have hxI : x ∈ ((MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap ρ).map Mc.subtype := by
    refine ⟨⟨x,hxMc⟩,?_,rfl⟩
    exact hQI (mem_map_of_mem ρ (show (⟨x,hxMc⟩ : Mc) ∈
      ((F.I₂ (sourceResidual M Mc)).pCoreIn 2).subgroupOf Mc from hxQ))
  exact hplace ⟨hxT,hxI⟩

end CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
