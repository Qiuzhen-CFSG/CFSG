module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification.Nonsolvable
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification.RankOneFactors
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleSource.RankOne
/-!
# Genuine natural-factor source selection for E.2.3

Apply genuine B.5.6 to the original offender action, then exclude every
higher-rank and exceptional action using the actual minimal-parabolic
geometry. The quasisimple section is naturally SL2 or marked symmetric-five;
the two-factor branch retains its original two natural rank-one summands.
All quotient maps, component inclusions and central-quotient actions remain
those of the source. No recognition or parabolic-invariance premise remains.

Source: Aschbacher–Smith, B.6.9 and E.2.3, pp.115–116 and 216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {K : GroupClass.{u}}

/-- Both original source alternatives carry only natural SL2 or symmetric-five factors. -/
theorem nonsolvable_natural_factors
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
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ F : ChapterB.QuasisimpleSource.BinaryField, ChapterB.QuasisimpleSource.IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) F 2) ∨
        Nonempty (ChapterB.QuasisimpleSource.MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  have ha := nonsolvable_rankOne_factors_or_quasisimple earlier hG T hP U q hq hker hcore hs hJ
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
  rcases ha with ⟨hqs,⟨c⟩⟩ | hpair
  · exact Or.inl ⟨hqs,c,ChapterB.source_offender_quasisimple_rank_one
      ρ (T.mapSurjective hq) hp hff hcore hqs c⟩
  · exact Or.inr hpair

/-- Known-simple source application using only the genuine earlier classification inputs. -/
theorem source_nonsolvable_natural_factors_of_earlier
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
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ F : ChapterB.QuasisimpleSource.BinaryField, ChapterB.QuasisimpleSource.IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) F 2) ∨
        Nonempty (ChapterB.QuasisimpleSource.MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  let := hU.normal
  let := hU.elementary
  exact nonsolvable_natural_factors
    (ChapterB.SourceInduction.adequateClassification_knownSimple_of_earlier_classification hA h36 h4)
    hG T hP U _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hs hJ
end CFSG.Quasithin.ChapterE.ThompsonAction
