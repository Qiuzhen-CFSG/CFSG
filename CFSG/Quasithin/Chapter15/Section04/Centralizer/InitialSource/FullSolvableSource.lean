module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.Join
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness.SourceE29.Solvable.Source

/-!
# Initial Theorem E source with solvable E.2.9 discharged

The proved original two-conjugate witness and its all-member generalized
Fitting inheritance instantiate E.2.9 in the actual solvable ratio argument.
Together with the already proved D.1 source alternatives this constructs
the actual local family, the large-center contradiction, and the same
small-center maximal local at which the fixed characteristic pair fails.
That local is now proved to be the member's minimal parabolic.

No E.2.9 or D.1 theorem is an input. The earlier source classifications,
3.1.1, and the small-center uniform-pair/block route remain explicit with
their source owners. Source: Aschbacher--Smith 15.4.2--25, pp.1155--1165.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.FullSolvableSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_family_data
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
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
  exact SolvableSource.source_family_data hA hC h311
    RatioSource.OutsideWitness.source_earlierE29Solvable hB hG T hempty hmany

theorem source_large_center_contradiction
    (hABC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
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
  exact SolvableSource.source_large_center_contradiction hABC h311
    RatioSource.OutsideWitness.source_earlierE29Solvable hB classification embedding orbits residual
    c27 c134 sourceB sourceF hG T hempty hmany hlarge

/-- All original source geometry on the actual fixed-pair failure local,
with the complete solvable ratio witnesses constructed. -/
theorem source_small_center_minimal_obstruction
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : Subgroup (ChapterB.baumann (T : Subgroup G))) [D.Characteristic] (hne : D ≠ ⊥) :
    ∃ (M X : Subgroup G) (s : ℕ) (h : Input KnownSimple.IsKnownSimple T M X s),
      Group.rank (localV T M) = 2*s ∧
      ChapterB.IsMinimalParabolicOver (T.subtype h.sylow_le) ⊤ ∧
      (centralizer (((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M) : Set M) ⊔
        normalizer (((D.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf M) : Set M)) < ⊤ ∧
      (Nonempty (CoreQuotient M ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
        Nonempty (CoreQuotient M ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup)) := by
  obtain ⟨M,X,s,h,hr,hp,he⟩ := SmallCenter.source_fixed_pair_failure_models
    hA hC h311 RatioSource.OutsideWitness.source_earlierE29Solvable hB hG T hempty hmany hZ D hne
  exact ⟨M,X,s,h,hr,SmallCenter.member_minimal_parabolic h hZ,hp,he⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource.FullSolvableSource
