module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.ReducedAction

/-!
# The original component in the classified offender group

The reduced component image is normal in the original centralizer quotient.
Its PSL₂(p) identification gives simplicity, and the original C-component
supplies perfectness. Thompson movement places this same component inside
the best-offender group, where the complete B.5.5 theorem now constructs its
faithful chief-section data and the component model list. Its nontriviality
also removes the degenerate alternative in the complete B.5.6 classifier.

All quotient maps are those of `ReducedAction`. The only retained earlier
premise is L=[L,J(T)], owned by `qt-d-1317-supplements`. These results do not
yet assert the four moved-module markings.
Source: Aschbacher--Smith 13.1.10, printed pp.871--872, using B.5.5--6.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

theorem reducedComponent_simple_perfect
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsSimpleGroup (NormalizerReducedAction.componentImage L) ∧
      Group.IsPerfect (NormalizerReducedAction.componentImage L) := by
  obtain ⟨p, hp, hp3, F, hF, hfin, hc, ⟨e⟩⟩ :=
    (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).2.2.1
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) := hL.1.1.1.perfect
  let eL := subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  let q := NormalizerReducedAction.radicalQuotientEquiv hL.1.1
    (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).2.2.2.1
    (solvableRadical_centralizes_normalizerReduced h hmany hL.1 hn)
  exact ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := q.toMonoidHom) q.surjective⟩

omit [Finite G] in
theorem reducedComponent_normal (L : Subgroup G) :
    (NormalizerReducedAction.componentImage L).Normal := by
  rw [NormalizerReducedAction.componentImage_eq]
  let : (L.subgroupOf (NormalizerReducedAction.Ambient L)).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem reducedComponent_isComponent
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsComponent (NormalizerReducedAction.Star L) (NormalizerReducedAction.componentImage L) := by
  obtain ⟨hs, hp⟩ := reducedComponent_simple_perfect h hmany hL hn
  let := hs
  let := hp
  have hz : center (NormalizerReducedAction.componentImage L) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  refine ⟨(reducedComponent_normal L).isSubnormal, { simple := ?_ }⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup

theorem reducedOffender_component
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    IsComponent (offenderSubgroup (reducedRepresentation L))
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) := by
  have hc := reducedComponent_isComponent h hmany hL hn
  let : IsQuasisimple (NormalizerReducedAction.componentImage L) := hc.2
  have hle := componentImage_le_reducedOffender h hL hn hmove
  exact ⟨hc.1.subgroupOf, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm⟩

theorem reducedOffender_nontrivialAlternative
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    NontrivialAdequateAlternative
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype) := by
  let := (reducedComponent_simple_perfect h hmany hL hn).1
  let : Nontrivial (offenderSubgroup (reducedRepresentation L)) :=
    (inclusion_injective (componentImage_le_reducedOffender h hL hn hmove)).nontrivial
  exact (reducedOffender_adequateAlternative h hL hn).of_nontrivial _

/-- The complete B.5.5 input is discharged on the original offender action. -/
theorem reducedOffender_preparation
    {T : Sylow 2 G} (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ComponentReduction.PreliminaryActions.Preparation.ComponentConclusion
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype) := by
  have earlier := ChapterB.PreparationSource.componentInput_of_classification_sources
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    ChapterB.SourceClassification.irreducibleClassification_knownSimple
  exact earlier _ _ _ (reducedOffender_hypothesis h hL hn)

/-- B.5.5 supplies the model list on the actual included component. -/
theorem reducedOffender_componentModels
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    ComponentReduction.PreliminaryActions.Preparation.ComponentModels
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))) := by
  obtain ⟨A, _, _, ⟨chief⟩⟩ := (reducedOffender_preparation h hL hn).chief _
    (reducedOffender_component h hmany hL hn hmove)
  exact chief.model

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
