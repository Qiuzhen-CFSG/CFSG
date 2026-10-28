module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.NormalizerControl
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.OrbitSource

/-!
# The double-source endpoint from actual component orbits

The unchanged original module inputs construct the residual pairs, ambient
normalizers, Baumann normalizer containments, binary coordinates, central
hyperplanes and order-four center. The adequate intrinsic route then supplies
all four Sylow conclusions and the corrected full-source endgame. The legacy restricted F618Universal is never instantiated. This discharges the local
geometry inputs formerly required by that endpoint.

The original family construction, unique-overgroup assertion, small-center
exclusion and complete earlier universal source implications remain with their
source owners. In particular this is not the full empty-family Theorem E.
Source: Aschbacher--Smith, 15.4.12--25, pp.1160--1165.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The actual double family requires no supplied pair, normalizer, fixed
hyperplane, central order-four witness or Sylow certificate. -/
theorem source_initial_double_contradiction_sourceOrbit
    (h311 : RatioSource.Earlier311 (G := G))
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hlarge : 2 < Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceB : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (sourceF : Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) :
    False := by
  obtain ⟨pX⟩ := exists_pair hX
  obtain ⟨pY⟩ := exists_pair hY
  obtain ⟨hc, _, _, hCX, hCY⟩ := source_double_center_geometry hX hY huniqueX huniqueY hne hlarge
  exact source_pair_contradiction_of_adequate_embedding_full_source_sourceOrbit hX hY pX pY
    (source_member_normalizer hX) (source_member_normalizer hY)
    (source_double_baumann_normalizer h311 hX huniqueX)
    (source_double_baumann_normalizer h311 hY huniqueY)
    huniqueX huniqueY hne hc hCX.2 hCY.2 residual hABC c27 c134 sourceB sourceF

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses

