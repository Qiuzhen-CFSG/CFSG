module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.QuasisimpleAction.Structure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# Full B.5.1 on the actual C.2.7 moved section

The proved known-simple A, C and B.4.2 theorems discharge every earlier input
of the full B.5.1 classification. The action is the literal star action
restricted to its actual offender subgroup, retaining the embedded original
star component. The conclusion preserves the moved-section action and all
six source clauses; no parabolic or C.2.7 marked alternative is inferred.

Source: Aschbacher--Smith C.2.7, displayed (!), p.146, and B.5.1, pp.99–103.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {H K R M : Subgroup G}

theorem star_offender_hypothesis_knownSimple
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal] :
    let ρ := starRepresentation K R
    let J := offenderSubgroup ρ
    QuasisimpleSourceHypothesis (ρ.comp J.subtype) KnownSimple.IsKnownSimple
      ((starImage K R K).subgroupOf J) :=
  star_offender_hypothesis (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) h

theorem star_moved_section_conclusion
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal] :
    let ρ := starRepresentation K R
    let J := offenderSubgroup ρ
    starImage K R K ≤ J ∧
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp J.subtype) ((starImage K R K).subgroupOf J)) := by
  refine ⟨(star_offender_fitting h).1,?_⟩
  exact knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple
    SourceInduction.nonbinaryG2RootPairInput _ _ _ _ (star_offender_hypothesis_knownSimple h)

end CFSG.Quasithin.ChapterC.C27Source
