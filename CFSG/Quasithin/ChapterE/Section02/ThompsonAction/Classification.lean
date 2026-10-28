module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.OffenderSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.CompleteSourceInputs

/-!
# Earlier classification on the original E.2.3 offender action

The actual faithful centralizer quotient has a nontrivial offender subgroup.
Its restriction satisfies every B.5.3 hypothesis, so the complete B.5.6 source
producer applies. The known-simple version retains only the genuine earlier
semisimple, A.3.6 and corrected B.4.2 inputs; neither a module chart nor a
B.5.6 classification conclusion is assumed.

Source: Aschbacher–Smith, B.6.9 and E.2.3, printed pp.116 and 216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {K : GroupClass.{u}}

/-- The full earlier B.5.6 classifier applies to the actual nontrivial E.2.3 offender action. -/
theorem classify_offender_source
    (earlier : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      (ρ.comp (offenderSubgroup ρ).subtype) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hs := (offender_source_hypotheses hG T hP U q hq hker hcore hJ).1
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  let : Nontrivial (offenderSubgroup ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (offenderSubgroup_ne_bot_of_ff ρ hff)
  exact (earlier _ _ _ hs).of_nontrivial _

/-- The complete known-simple B.5.6 producer discharges the classification input. -/
theorem source_offender_classification_of_earlier
    (hA : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput.{u}
      KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      (ρ.comp (offenderSubgroup ρ).subtype) := by
  let := hU.normal
  let := hU.elementary
  exact classify_offender_source
    (ChapterB.SourceInduction.adequateClassification_knownSimple_of_earlier_classification hA h36 h4)
    hG T hP U _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hJ

end CFSG.Quasithin.ChapterE.ThompsonAction
