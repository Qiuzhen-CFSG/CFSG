module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.Thompson
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete

/-!
# Intrinsic embedding discharge for the actual Theorem E source branch

The original multiple-overgroup assembly used an adequate local embedding as
an explicit parameter.  The complete intrinsic known-simple theorem constructs
that embedding from the local input, the SQTK hypothesis and the genuine Sylow
condition.  This wrapper preserves the old source theorem and removes only
that discharged parameter; all other earlier source inputs remain explicit.

Source: Aschbacher--Smith Proposition 1.3.4 and Theorem 15.4.25.
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

/-- The multiple-overgroup branch with its intrinsic adequate embedding
    discharged by the complete known-simple source theorem. -/
theorem source_many_theoremE_from_thompson_intrinsic
    (h311 : RatioSource.Earlier311 (G := G))
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
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
  exact source_many_theoremE_from_thompson h311 h1391 classification
    Chapter1.XiEmbedding.adequateLocalEmbeddingTheorem_knownSimple orbits residual
    c27 c134 sourceB sourceF hG T hempty hmany D hD

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
