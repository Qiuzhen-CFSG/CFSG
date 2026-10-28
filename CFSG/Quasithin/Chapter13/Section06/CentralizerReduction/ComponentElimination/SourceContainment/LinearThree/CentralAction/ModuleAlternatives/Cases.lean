module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.PSL3Two.SmallModules

/-!
# The two L₃(2) module alternatives and their preparation boundary

The preparation record contains group and action hypotheses only. The
separate extraction target retains the actual moved space, its component
fixed quotient, and one compatible actor and module identification. Its
natural branch retains commutator generation; its doubled branch identifies
the moved space itself. Constructing this target from the universal B.5.1
and adequate B.5.6 implications remains a separate source obligation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1 and B.5.6,
printed pp.99–105, and 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB.QuasisimpleSource
/-- The two outputs needed from B.5.1/B.5.6. The first is a statement on
the literal quotient by the component fixed space; the second is on the
moved space itself. This is an extraction target, not a proved classification. -/
inductive LinearThreeModuleCase {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V) (C : Subgroup D) : Prop
  | natural (sectionData : MovedSection ρ C)
      (generated : subspaceCommutator ρ sectionData.space.toSubmodule C =
        sectionData.space.toSubmodule)
      (coordinates : ActionEquiv (sectionData.action.comp C.subtype) BinaryLinearThree.W)
  | doubled (sectionData : MovedSection ρ C)
      (coordinates : ActionEquiv (sectionData.space.toRepresentation.comp C.subtype)
        (repeated BinaryLinearThree.W 2))

universe u w

/-- Applicability data before restricting the faithful action to its offender
subgroup. This contains no classification or module identification. -/
structure ClassifierApplicability {D : Type u} [Group D] [Finite D]
    {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    (𝒦 : GroupClass.{u}) (ρ : Representation (ZMod 2) D V) (C : Subgroup D) : Prop where
  finite_module : Module.Finite (ZMod 2) V
  faithful : Function.Injective ρ
  twoCore : pCore 2 D = ⊥
  normal : C.Normal
  le_offenders : C ≤ offenderSubgroup ρ
  quotient : Nonempty (ChapterB.SourceInduction.SQTKQuotient 𝒦 D)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
