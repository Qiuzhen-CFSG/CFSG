module
public import CFSG.Quasithin.Chapter10.SourceA5BaumannDisplacement
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterAction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveMovingActor
/-!
# A transvection on the actual fixed-center HStar module

In the positive fixed-center branch, an escaping Baumann normalizer supplies
an actual HStar subgroup and its reduced Sylow-center orbit W. The original
residual Sylow acts nontrivially on W. The paired residual product and its
Baumann-center displacement lines now select an actual actor in T∩L₀
whose nonzero displacement on W is a single line. All local-to-ambient
inclusions and commutators are retained.

This discharges the transvection-selection step in original 10.2.1.
The later action classification and overcomponent contradiction remain.
Source: Aschbacher--Smith, 10.2.1, printed p.743.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_exists_fixed_center_transvection
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
      H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
       W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
       IsPReduced 2 (W.subgroupOf H) ∧
       ∃ g ∈ (T : Subgroup G) ⊓ localOrbit T L, ∃ v ∈ W, v ≠ 1 ∧
         (∀ x ∈ W, ⁅g,x⁆ = 1 ∨ ⁅g,x⁆ = v) ∧ ∃ x ∈ W, ⁅g,x⁆ = v) := by
  obtain ⟨H,hH,hHN,hWE,hred,_,_⟩ := source_baumann_HStar_fixed_center_setup D hne hout
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let J := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf J
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set J)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set J) := QuotientGroup.ker_mk' C
  obtain ⟨d,t,ht₁,ht₂,⟨c⟩⟩ := source_a5_paired_five_action D e hn hout
  have hWT : W ≤ (T : Subgroup G) :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1
  have hWJ : W ≤ J := hWT.trans le_sup_right
  have hW0 : W.subgroupOf J ≤ omegaOneCenterAmbient (ChapterB.baumann (S : Subgroup J)) := by
    apply (Subgroup.map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWJ,source_local_baumann_center_map]
    exact hWE
  have hnorm : (S : Subgroup J) ≤ normalizer (W.subgroupOf J : Set J) := by
    intro x hx
    exact le_normalizer_comap J.subtype
      (le_normalizer_conjugateSpanBy _ _ (hH.1.1.2 hx))
  have hmove : ¬ (S : Subgroup J) ⊓ pResidual 2 J ≤
      centralizer (W.subgroupOf J : Set J) := by
    intro hfix
    apply source_a5_fixed_center_orbit_action D e hn hne H hH
    intro g hg x hx
    have hgR : (⟨g,mem_sup_right hg.1⟩ : J) ∈ pResidual 2 J := by
      have hh := hg.2
      rw [←source_join_residual D] at hh
      obtain ⟨a,ha,he⟩ := hh
      have he' : a = (⟨g,mem_sup_right hg.1⟩ : J) := Subtype.ext he
      exact he' ▸ ha
    exact congrArg Subtype.val (hfix ⟨hg.1,hgR⟩ ⟨x,hWJ hx⟩ hx)
  obtain ⟨g,hg,v,hv,hvne,hline,x,hx,he⟩ := paired_baumann_moving_actor S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c ⟨t,ht₁,ht₂⟩ (W.subgroupOf J) hW0 hnorm hmove
  refine ⟨H,hH,hHN,hWE,hred,(g:G),⟨hg.1,?_⟩,(v:G),hv,?_,?_,(x:G),hx,?_⟩
  · rw [←source_join_residual D]
    exact mem_map_of_mem J.subtype hg.2
  · exact fun he => hvne (Subtype.ext he)
  · intro y hy
    exact (hline ⟨y,hWJ hy⟩ hy).imp (congrArg Subtype.val) (congrArg Subtype.val)
  · exact congrArg Subtype.val he
end CFSG.Quasithin.Chapter10
