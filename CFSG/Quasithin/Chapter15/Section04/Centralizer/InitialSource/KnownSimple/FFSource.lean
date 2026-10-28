module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.WreathExclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# The actual Theorem E source branch with complete B.5 discharged

The complete known-simple B.5 theorem supplies all six quasisimple clauses
and every adequate general alternative on the original representation. Its
literal transport into the existing mixed-factor source interface removes
the last FF classification parameter. The genuine remaining earlier source
inputs and the single uniform characteristic pair retain their quantifiers.

Source: Aschbacher--Smith B.5.1--12 and15.4.18--25.
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

theorem source_many_theoremE_from_classifiedFF
    (h311 : RatioSource.Earlier311 (G := G))
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (c27 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  exact source_many_theoremE_from_source1391 h311 classification orbits residual c27 c134
    FFBranch.ClassificationComparison.FFAlternatives.SourceB5.classification sourceF
    hG T hempty hmany D hD

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
