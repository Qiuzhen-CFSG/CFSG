module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete

/-!
# The original Theorem E local family with solvable Thompson factorization discharged

The complete proved B.2.16, including its literal internal group/module
coordinates, Sylow assertion and rank clauses, is applied at the original
source locals. All earlier A/B/C and solvable D.1/E.2.9 inputs were already
constructed. These consumers remove the remaining B.2.16 parameter from
the actual all-member family and both center-size branches.

The genuine common-normal theorem, uniform characteristic pair, 13.9.1,
and the remaining large-center earlier classifications are explicit.
The independent unique-centralizer-overgroup branch remains with Section15.3.
Source: Aschbacher--Smith B.2.16 and15.4.2--25, printed pp.79,1155--1165.
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

/-- Construct every original local input using the proved full-catalogue A/C. -/
theorem source_family_data_from_thompson
    (h311 : RatioSource.Earlier311 (G := G))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T ∧
    (∀ M ∈ maximalLocals T, ∃ X : Subgroup G, ∃ s : ℕ,
      Input KnownSimple.IsKnownSimple T M X s) ∧
    (∀ M ∈ maximalLocals T, ∀ X ∈ Y (T : Subgroup G), X ≤ M →
      ∃ s : ℕ, Input KnownSimple.IsKnownSimple T M X s) := by
  exact FullSolvableSource.source_family_data
    (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
    (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H))
    h311 Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216 hG T hempty hmany

/-- The small-center source branch, with no A/C input remaining. -/
theorem source_small_center_theoremE_from_thompson
    (h311 : RatioSource.Earlier311 (G := G))
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  exact SmallCenter.source_small_center_theoremE
    (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
    (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H))
    h311 Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216 h1391 hG T hempty hmany hZ D hD

/-- Both center-size cases of the actual multiple-overgroup source branch. -/
theorem source_many_theoremE_from_thompson
    (h311 : RatioSource.Earlier311 (G := G))
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
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
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  have hnonzero := Subgroup.one_lt_card_iff_ne_bot
    (omegaOneCenterAmbient (T : Subgroup G)) |>.mpr (centralOmega_ne_bot hG T)
  by_cases hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))
  · exact (FullSolvableSource.source_large_center_contradiction
      (fun H _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := H))
      h311 Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216 classification embedding orbits residual c27 c134 sourceB sourceF
      hG T hempty hmany hlarge).elim
  · exact source_small_center_theoremE h311 Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216 h1391 hG T hempty hmany
      (by omega) D hD
end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
