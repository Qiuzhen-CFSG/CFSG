module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FusionSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.SourceContainment

/-!
# Rudvalis conclusion after the original centralizer and reversal arguments

The source constructions now discharge fixed-element centralizer containment,
critical reversal, the critical order and fusion. The original 14.7.75/J.1.1
consumer retains the genuine earlier classification and Goldschmidt inputs;
no target-shaped centralizer, odd quotient, symmetry or order premise remains.
Source: Aschbacher–Smith 14.7.68–75 and J.1.1.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt
open CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open SteinbergRecognition SteinbergRecognition.ModuleRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal source endpoint with 14.7.68, reversal, order and fusion constructed. -/
theorem source_rudvalis_of_original_centralizers
    (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
    (selection : c.RankSelection)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u})
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Source
      KnownSimple.IsKnownSimple G) : Nonempty (G ≃* Rudvalis.Model) := by
  have h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H :=
    d.fixedCentralizer_le_H_of_original_source structural faithful modules baumann weakClosure c27
  exact source_rudvalis_of_original_fusion d c structural faithful amalgams sourceF selection
    (d.order_two_of_source_reversal structural faithful modules baumann weakClosure h68 c selection)
    modules baumann weakClosure h68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
