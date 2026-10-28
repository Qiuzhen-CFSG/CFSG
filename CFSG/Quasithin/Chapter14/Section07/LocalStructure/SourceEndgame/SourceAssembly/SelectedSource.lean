module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FixedCentralizerSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Source

/-!
# The Rudvalis endpoint with the critical path selected from source data

The original LT/H geometry constructs the critical path. The actual point
commutator, obtained from the preceding module classification, selects its
orientation and proves both rank conditions. Uniqueness is supplied by the
proved Theorems A and C. The final 14.7.75/J.1.1 consumer therefore has no
critical-path, rank, commutator, centralizer, or fusion premise.

The genuine preceding classification, Baumann/weak-closure and Goldschmidt
source inputs remain explicit. Source: Aschbacher–Smith, Notation14.7.1,
14.7.68–75 and J.1.1, printed pp.1043,1071–1076,432.
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

/-- The literal original Data supplies the selected critical path internally. -/
theorem source_rudvalis_of_original_data
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (weakClosure : Theorem14731.{u})
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Source
      KnownSimple.IsKnownSimple G) : Nonempty (G ≃* Rudvalis.Model) := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  have hUQ := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  obtain ⟨c,hc⟩ := d.exists_selected_criticalPath structural uniqueness hUQ
  exact source_rudvalis_of_original_centralizers d c structural faithful amalgams sourceF hc
    modules baumann weakClosure c27

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
