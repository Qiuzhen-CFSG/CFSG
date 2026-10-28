module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedModuleRowsG2
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneCentralizers

/-!
# Original fixed-module rows with the G₂ source inputs discharged

The source 12.4.8 hyperplane-centralizer theorem and the moved-family
Sylow-normalizer theorem supply the two G₂ callbacks in the guarded row
sieve. The conclusions use the literal original chosen modules and retain
only their earlier-source structural, module and rank-one-exit hypotheses.

Source: Aschbacher--Smith 12.4.1--2, 12.4.8--9 and 13.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02
open Chapter12.Section04.SmallFusion
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter14.Section03.CaseOneSource
open Chapter14.Section03.FaithfulSource
open ChapterB.QuasisimpleSource
open Chapter13.Section03.Noncentrality.SupercriticalSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

theorem fixedSpaceRows1332At_of_guarded_source
    (h1331 : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (exits : ∀ K : Subgroup G, ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    : FixedSpaceRows1332At (T := T) := by
  apply fixedSpaceRows1332At_of_guarded_hyperplanes_source h1331 hmany structural modules exits
  intro K W hK D hne E U hUW hcor
  exact Chapter12.Section04.SmallFusion.G2Source.cover_hyperplane_centralizers
    hK D structural E hne hUW hcor

theorem originalFixedModule1332At_of_guarded_source
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
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    : OriginalFixedModule1332At T L := by
  exact originalFixedModule1332At_of_fixed_space_rows h1331 hmany quasisimple models
    structural modules
    (fixedSpaceRows1332At_of_guarded_source h1331 hmany structural modules exits)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
