module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The fixed-module clause of source 13.3.2(3)

This universal earlier input classifies every chosen faithful-local module
with nonzero fixed space as the five-dimensional augmentation core. It keeps
the faithful quotient K/C_K(W); replacing it by K/O₂(K) would lose the allowed
central-cover case. Its proof requires the 12.4.2 indecomposable exclusions in
addition to the 12.2.2 list, and remains with qt-d-1332-source.

This file defines that source obligation, not a theorem asserting it.
Its concrete reduction (g) application is in ModuleSieve/CoreReduction.
Source: Aschbacher--Smith, 13.3.2(3), printed p.885.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Chapter12.Section02 ChapterB.QuasisimpleSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-space specialization of 13.3.2(3), on the literal chosen module. -/
def FixedModule1332At (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Counterexample T L → ∀ B ∈ MainForward.faithfulLocalComponents T,
    ∀ W : Subgroup G, ∀ D : ChosenModule T B W,
      letI := D.actionCentralizer_normal
      W ⊓ centralizer (B : Set G) ≠ ⊥ →
      Nonempty (ActionEquiv D.faithfulAction
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6)))

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
