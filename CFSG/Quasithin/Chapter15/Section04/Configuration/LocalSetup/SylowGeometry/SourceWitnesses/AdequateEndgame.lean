module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.AdequateSylow
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.TwoCoreRecognition

/-!
# The final source-pair contradiction through the adequate intrinsic route

The original two pairs construct the genuine geometry, source 15.4.19,
all-four-choice Sylow assertion and LocalData. The proved 15.4.21--23 and
intersection endgame then give a contradiction. The source J is literally
the original Thompson subgroup, and the complete marked 1.1.5 is supplied
from the genuine universal A/B/C theorem.

The final input boundary retains full known-simple SQTK, adequate intrinsic
embedding with Held, complete component-orbit and residual statements,
C.2.7, C.1.34, adequate complete B.5 and F.6.18. Those independent earlier
source producers must still be proved and instantiated for Theorem E.
This theorem does not assume any later Sylow, LocalData or recognition output.
Source: Aschbacher--Smith, 15.4.19--24, pp.1163--1165.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- Close the source-pair argument after constructing every later local
input; the remaining parameters are complete earlier-source implications. -/
theorem source_pair_contradiction_of_adequate_embedding
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZX : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hCZY : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Y : Set G) ≠ ⊥)
    (embedding : Chapter1.XiEmbedding.AdequateLocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceB : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (source618 : TwoFactors.FFBranch.ClassificationComparison.F618Universal.{u}
      KnownSimple.IsKnownSimple) :
    False := by
  obtain ⟨hdata⟩ := source_geometry_localData_of_adequate_embedding hX hY pX pY hM₁ hM₂
    hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY embedding orbits residual hABC
    c27 c134 sourceB.quasisimple
  exact SourceRecognition.TwoCore.source_endgame hdata hX.ambient source618 sourceB
    (SourceRecognition.Source.earlier115 hX.ambient hABC) rfl

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
