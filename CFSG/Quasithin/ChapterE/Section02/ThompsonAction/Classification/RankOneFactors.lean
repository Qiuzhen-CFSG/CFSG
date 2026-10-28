module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.ExceptionalFactor
/-!
# Genuine nonsolvable rank-one factor selection for E.2.3

Apply the earlier B.5.6 source theorem to the actual faithful offender action.
The hyperplane row and every SL3 source factor, including its exceptional
four-dimensional extension, contradict the original minimal-parabolic
normalizer geometry. Thus either the full quasisimple B.5.1 conclusion holds,
or the original product has two natural SL2/symmetric-five summands. The
product and decomposition in V/C_V(Y) are those of the earlier source theorem.
No component-orbit, module chart or field restriction is added as a premise.

Source: Aschbacher–Smith, B.6.9 and E.2.3, pp.115–116 and 216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {K : GroupClass.{u}}

/-- The original offender product has only natural rank-one factor rows. -/
theorem nonsolvable_rankOne_factors_or_quasisimple
    (earlier : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting Y))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  have ha := nonsolvable_offender_alternatives earlier hG T hP U q hq hker hcore hs hJ
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker,he]
    exact le_top
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hn).2
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  rcases ha with hqs | hrest
  · exact Or.inl hqs
  rcases hrest with ht | hh
  · obtain ⟨c⟩ := ht
    exact Or.inr ⟨c,ChapterB.source_offender_two_factor_rank_one ρ (T.mapSurjective hq) hp hff hcore c⟩
  · obtain ⟨c⟩ := hh
    exact (ChapterB.source_offender_hyperplane_excluded ρ (T.mapSurjective hq) hp hff hcore c).elim

/-- Known-simple source application using only the genuine earlier classification inputs. -/
theorem source_nonsolvable_rankOne_factors_or_quasisimple_of_earlier
    (hA : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput.{u}
      KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U) (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting Y))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  let := hU.normal
  let := hU.elementary
  exact nonsolvable_rankOne_factors_or_quasisimple
    (ChapterB.SourceInduction.adequateClassification_knownSimple_of_earlier_classification hA h36 h4)
    hG T hP U _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hs hJ
end CFSG.Quasithin.ChapterE.ThompsonAction
