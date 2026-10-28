module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections.Quasisimple
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentCenters
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.Normalization
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The original component-section input over the known-simple catalogue

B.5.5 supplies the group list for the original component of the faithful
FF actor. All nontriple alternatives convert directly to the models used
in 15.3.49(l). A component with cubic center forces the quasisimple branch
of the corrected adequate B.5 classification: the other branches have
centerless components. Component calculus identifies it with F*(D), so
B.5.1 supplies its original module section. The quasisimple adapter retains
that section when recognizing the even hexacode action.

The known-simple assembly uses the proved Theorems A and C and corrected
B.4.2; it retains Held in the source catalogue. No legacy universal B.5
interface or exceptional-section assumption is used.

Source: Aschbacher–Smith B.4.2, B.5.1, B.5.5(1)(iii–iv), B.5.6, and
15.3.49(l), combined manuscript of 1 March 2004, pp.86, 99, 104–106, 1144.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open ComponentReduction ModelReduction BinaryModels ModelSieve
open ChapterB.SourceInduction
universe u

/-- The two corrected appendix conclusions supply the literal earlier input. -/
theorem earlierComponentSections_of_source_inputs {κ : GroupClass.{u}}
    (component : ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentInput.{u,u} κ)
    (adequate : AdequateClassificationInput.{u,u} κ) : EarlierComponentSections κ := by
  intro D W _ _ _ _ ρ hm hf hcore hgen Cover _ _ hsq N _ e C hC
  let : Module.Finite (ZMod 2) W := hm
  let hyp : FFHypothesis κ ρ := {
    finite_module := hm
    faithful := hf
    twoCore := hcore
    generated := hgen
    quotient := ⟨{
      Cover := Cover
      kernel := N
      sqtk := hsq
      equiv := e }⟩ }
  let : IsQuasisimple C := hC.2
  obtain ⟨A, _, _, ⟨chief⟩⟩ := (component D W ρ hyp).chief C hC
  apply componentSection_of_models ρ C chief.model
  intro hc
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  let : Nontrivial D := Function.Injective.nontrivial C.subtype_injective
  have ha := (adequate D W ρ hyp).of_nontrivial ρ
  obtain ⟨hq, ⟨q⟩⟩ := ha.quasisimple_of_component_center_card_three hC hc
  let : IsQuasisimple (generalizedFitting D) := hq
  have he : C = generalizedFitting D := hC.eq_of_le
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    (component_le_generalizedFitting D C hC)
  subst C
  exact componentSection_of_quasisimple_source ρ _ q

/-- The actual earlier input, with every source-classification premise discharged. -/
theorem earlierComponentSections_knownSimple :
    EarlierComponentSections KnownSimple.IsKnownSimple :=
  earlierComponentSections_of_source_inputs
    (ChapterB.PreparationSource.componentInput_of_classification_sources
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
      ChapterB.SourceClassification.irreducibleClassification_knownSimple)
    adequateClassification_knownSimple

namespace Input
variable {G : Type u} [Group G] [Finite G]
  {H M Y V Y0 T ZS Z E L upper : Subgroup G}
  [IsElementaryAbelian 2 (localSpan ZS H)]
  (d : Input KnownSimple.IsKnownSimple H M Y V Y0 T ZS Z E L upper)

/-- The contained-offender reduction receives its actual component section. -/
theorem component_sections_knownSimple :
    ComponentSectionAlternative d.placed.action.representation (starImage H L) :=
  d.component_sections earlierComponentSections_knownSimple

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
