module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SolvableParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.OutsideParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NaturalSource
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairNatural
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Source
/-!
# The original outside moved chi-block source

Characteristic two and proper characteristic-normalizer control select an
escaping minimal parabolic. Its canonical omega-center span is reduced and
Thompson-moved. The complete B.5/B.6 source classification gives exactly the
solvable, quasisimple linear, quasisimple five, paired linear, or paired five
branch. Each proved local branch supplies a genuine moved block supported
in the canonical module, and C.1.27 lifts it to the original ambient group.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB SourceInduction QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
theorem outside_moved_chi_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M : Subgroup G) (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hproper : M ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  classical
  obtain ⟨H,hTH,hP,hout⟩ := exists_minimalParabolic_outside_control T hf M hM hproper
  by_cases hs : Group.IsSolvable H
  · exact ambient_outside_of_solvable_parabolic hA hC h4 hG T hf M H hTH hM hout hP hs
  let S := T.subtype hTH
  have hfH : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (centralizer_pCore_le_of_pCore_le H
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
        ((pCore_isPGroup.le_sylow_of_normal T).trans hTH))
  have hchar := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfH
  let U := normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H)
  have hU : IsPReduced 2 U := omegaCenter_normalClosure_reduced S hchar
  let := hU.normal
  let := hU.elementary
  have hcontrol : (S : Subgroup H).characteristicNormalizerClosure ≤ M.subgroupOf H :=
    characteristicNormalizerClosure_subgroupOf_le hTH hM
  have hM' : M.subgroupOf H ≠ ⊤ := fun he => hout (subgroupOf_eq_top.mp he)
  have hS : (S : Subgroup H) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [show (T.subtype hTH : Subgroup H) = ⊥ from hz]
    exact le_normalizer_of_normal
  have hJ := thompson_moves_omega_closure_of_control S hS U rfl (M.subgroupOf H) hcontrol hM'
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨hqs,c,hlin|⟨e⟩⟩ | ⟨d,_⟩ := reduced_nonsolvable_natural_source (hG.subgroup H) S hP U hU hs hJ
  · obtain ⟨F,hnat⟩ := hlin
    exact ambient_outside_of_quasisimple_linear_section hA hC h4 hG T hf M H hTH hM hout hP
      U q hq hk hqs c.sectionData F hnat rfl
  · obtain ⟨e⟩ := e
    exact ambient_outside_of_quasisimple_five_section hA hC h4 hG T hf M H hTH hM hout hP
      U q hq hk hqs c.sectionData e rfl
  · have hqne : q.ker ≠ ⊤ := by
      intro he
      apply hJ
      change elementaryAbelianMaxJ (S : Subgroup H) ≤ C
      rw [←hk,he]
      exact le_top
    have hPQ := (minimalParabolic_reduced_image S hP q hq hU.quotient_pCore_eq_bot hqne).2
    have hff : IsFFModule α := by
      obtain hz | ⟨_,hf',_,_,_⟩ := lemma_B_2_7 U q hq hk S
      · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hz.1)).elim
      · exact hf'
    let := offenderSubgroup_normal α
    obtain ⟨t,ht₁,ht₂,hlin|⟨c⟩⟩ := source_offender_two_factor_shared_natural α
      (S.mapSurjective hq) hPQ hff hU.quotient_pCore_eq_bot d
    · obtain ⟨F,⟨c⟩⟩ := hlin
      exact ambient_outside_of_paired_linear hA hC h4 hG T hf M H hTH hM hout hP U q hq hk
        hs d F c ⟨t,ht₁,ht₂⟩ rfl
    · obtain ⟨c⟩ := c
      obtain ⟨L,hLo,hL,hLJ,hLU,hLUle⟩ := paired_five_outside_moved_chi
        (ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC) (hG.subgroup H)
        S hP U hU hJ q hq hk hs hfH d c ⟨t,ht₁,ht₂⟩ (M.subgroupOf H) hcontrol hM'
      exact ambient_outside_of_local_moved_chi hA hC h4 hG T hf M H hTH hM L hL hLo hLJ hLUle
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
