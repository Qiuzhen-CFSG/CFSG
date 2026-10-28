module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.PairDispatch
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.DoubleEndgame.FullSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.FullSource

/-!
# The original multiple-centralizer-overgroup branch through its actual pairs

Original empty-family hypotheses construct a member in every maximal local.
The initial source dispatch produces either a mixed pair or two double members
in distinct maximal locals. The complete source mixed argument excludes the
first possibility. The adequate intrinsic route constructs all later Sylow
and LocalData conclusions for the second, and the corrected source endgame
excludes it. No family member, pair, configuration or later conclusion is input.

The separate small-center source theorem and the full earlier implications
still require their producers. This proves the large-center branch of the
original source theorem, not the complete eight-model Theorem E.
Source: Aschbacher--Smith,15.4.12--24, printed pp.1161--1165.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_large_center_contradiction
    (hABC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (embedding : Chapter1.XiEmbedding.AdequateLocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
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
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) : False := by
  have hA := fun (H : Type u) [Group H] [Finite H] => (hABC H).1
  have hC := fun (H : Type u) [Group H] [Finite H] => (hABC H).2.2
  rcases source_initial_pair_cases hA hC h311 hD15 h29 hB classification
    hG T hempty hmany hlarge with hmixed | hdouble
  · obtain ⟨M₁,M₂,Y,X,p,hY,hX,_,⟨d⟩,c⟩ := hmixed
    have hZ := (source_lemma_15_4_14_of_large_center hA hC h311 hD15
      RatioSource.InsideCore.source_earlierD14Sylow h29 hB hG T hempty hmany hlarge).1
    exact source_mixed_contradiction hABC sourceF sourceB hY hX p d c hZ
  · obtain ⟨M₁,M₂,X,Y,hX,hY,hne,hux,huy⟩ := hdouble
    exact source_initial_double_contradiction_full_source h311 hX hY hux huy hne hlarge
      embedding orbits residual hABC c27 c134 sourceB sourceF

end CFSG.Quasithin.Chapter15.Section04.InitialSource
