module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.FactorImages
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumann
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveWhole
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Solvable
/-!
# The original Thompson–Baumann image identity in every source branch

The genuine solvable and quasisimple natural markers identify both images
with the defining Sylow image. The symmetric-five markers identify both
with the same transposition four-group or its paired product. The complete
known-simple classifier selects these cases from the original hypotheses,
so no classification, coordinate, or image premise remains.

Source: Aschbacher–Smith E.2.3(2),(3), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_thompson_baumann_image
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (baumann (T : Subgroup G)).map q := by
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  have hcore : pCore 2 (G ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  by_cases hs : Group.IsSolvable G
  · let := hs
    obtain ⟨d,hc,_,ht⟩ := source_solvable_factors T hP U hU hJ
      (hG.stronglyQuasithin 3 (by decide) (by decide)) inferInstance
    rcases hc with hc | hc
    · have him := solvable_single_images_of_factors T hP U hU q hq hk hcore hJ d hc
      exact him.1.trans him.2.symm
    · have him := solvable_pair_images_of_factors T hP U q hq hk hcore
        (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ d hc ht
      exact him.1.trans him.2.symm
  · rcases source_nonsolvable_natural_factors hG T hP U hU hs hJ with
      ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
    · obtain ⟨F,hF⟩ := hlin
      have him := quasisimple_linear_source_images T hP U hU hJ q hq hk hqs c.sectionData F hF
      exact him.1.trans him.2.symm
    · obtain ⟨e⟩ := hfive
      exact quasisimple_five_source_images T hP U hU hJ q hq hk hqs c.sectionData e
    · let := offenderSubgroup_normal α
      have hn : q.ker ≠ ⊤ := by
        intro he
        exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
      have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
      have hff : IsFFModule α := by
        obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hk T
        · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
        · exact hff
      obtain ⟨t,ht₁,ht₂,hmodel⟩ := source_offender_two_factor_shared_natural
        α (T.mapSurjective hq) hp hff hcore d
      rcases hmodel with hlin | hsym
      · obtain ⟨F,⟨c⟩⟩ := hlin
        obtain ⟨_,_,_,_,him,_⟩ := RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace
          T hP U hU hJ q hq hk d F c ⟨t,ht₁,ht₂⟩
        exact him.1.trans him.2.symm
      · obtain ⟨c⟩ := hsym
        exact (paired_thompson_baumann_of_symmetric_model T hP U hU hJ q hq hk d c ⟨t,ht₁,ht₂⟩).1
end CFSG.Quasithin.ChapterE.ThompsonAction
