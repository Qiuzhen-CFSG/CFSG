module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.FullSolvableSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.SourceEndgame
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The actual multiple-overgroup branch with A/B/C discharged

The unconditional full-catalogue A/B/C theorem supplies all earlier A/C
applications in the original empty-family configuration. The two possible
sizes of the actual central omega subgroup are then handled by the proved
large-center contradiction and the small-center recognition theorem.

The genuine remaining earlier source theorems are still explicit. In
particular, this does not assert the independent unique-overgroup branch
of Section 15.3. Source: Aschbacher--Smith 15.4.25, printed p.1165.
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
theorem source_family_data
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
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
    h311 hB hG T hempty hmany

/-- The small-center source branch, with no A/C input remaining. -/
theorem source_small_center_theoremE
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
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
    h311 hB h1391 hG T hempty hmany hZ D hD

/-- Both center-size cases of the actual multiple-overgroup source branch. -/
theorem source_many_theoremE
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
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
      h311 hB classification embedding orbits residual c27 c134 sourceB sourceF
      hG T hempty hmany hlarge).elim
  · exact source_small_center_theoremE h311 hB h1391 hG T hempty hmany
      (by omega) D hD
end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
