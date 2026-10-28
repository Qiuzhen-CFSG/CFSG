module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedModuleRows

/-!
# L₃ assembly for the original fixed-space sieve

The guarded L₃ fixed-space theorem is the exact 12.4.2 source implication.
This adapter packages it into the L₃ half of `FixedSpaceRows1332At`, leaving
only the independent G₂ Weyl fixed-space callback explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02
open Chapter12.Section04.SmallFusion
open Chapter12.Section04.SLThreeCommutatorSource
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter14.Section03.CaseOneSource
open Chapter14.Section03.FaithfulSource
open ChapterB.QuasisimpleSource
open Chapter13.Section03.Noncentrality.SupercriticalSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

/-- Package the guarded L₃ fixed-space source theorem together with a single
G₂ fixed-space callback into the row-sieve contract.  The `exits` argument is
kept pointwise in the component because 12.4.2 uses the normalizer of that
component literally. -/
theorem fixedSpaceRows1332At_of_l3_source
    (h1331 : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (exits : ∀ K : Subgroup G, ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T
        (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H) →
      Nonempty ((Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H ⧸
          pCore 2 (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T
          (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H) ∧
        RankOneModule.SmallExit T
          (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H))
    (g2_fixed : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ∀ (_E : ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))),
        fixedSubgroup K W = ⊥) :
    FixedSpaceRows1332At (T := T) := by
  unfold FixedSpaceRows1332At
  intro K W hK D hne
  refine ⟨?_, ?_⟩
  · intro _E hmodel
    exact slThreeFixedSpace1242_of_source_at
      h1331.hypothesis1311 hK D hmany structural modules hmodel (exits K)
  · intro E
    exact g2_fixed K W hK D hne E

/-- Directly discharge the original fixed-module callback from the guarded
L₃ source route, retaining only the independent G₂ fixed-space exclusion. -/
theorem originalFixedModule1332At_of_l3_source
    (h1331 : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (models : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I))
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (exits : ∀ K : Subgroup G, ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T
        (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H) →
      Nonempty ((Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H ⧸
          pCore 2 (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T
          (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H) ∧
        RankOneModule.SmallExit T
          (Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual H))
    (g2_fixed : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ∀ (_E : ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))),
        fixedSubgroup K W = ⊥) :
    OriginalFixedModule1332At T L := by
  exact originalFixedModule1332At_of_fixed_space_rows h1331 hmany quasisimple models
    structural modules
    (fixedSpaceRows1332At_of_l3_source h1331 hmany structural modules exits g2_fixed)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
