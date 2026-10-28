module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.Intrinsic
public import CFSG.Quasithin.Chapter13.Section09.Source

/-!
# Applying the proved wreath exclusion at the original source boundary

The genuine 13.9.1 theorem is applied to the literal original configuration.
Its callback is therefore discharged; the earlier public theorem and its
original subgroup, Sylow and module hypotheses are preserved.

Source: Aschbacher--Smith 13.9.1, 14.1.10 and 15.3--15.4.25.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open ChapterC.GlaubermanNiles
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_small_center_theoremE_from_source1391
    (h311 : RatioSource.Earlier311 (G := G))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  exact source_small_center_theoremE_from_thompson h311 (fun _ _ _ h d => Chapter13.Section09.source13_9_1 h d) hG T hempty hmany hZ D hD

theorem source_many_theoremE_from_source1391
    (h311 : RatioSource.Earlier311 (G := G))
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (c27 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceB : FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  exact source_many_theoremE_from_thompson_intrinsic h311 (fun _ _ _ h d => Chapter13.Section09.source13_9_1 h d) classification orbits residual c27 c134 sourceB sourceF hG T hempty hmany D hD

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
