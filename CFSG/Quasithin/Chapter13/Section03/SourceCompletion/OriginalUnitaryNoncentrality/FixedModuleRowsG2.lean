module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedModuleRowsL3
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.G2FixedEndgame
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.TerminalAssembly

/-!
# The guarded G₂ source application in the original fixed-module sieve

The binary Weyl row is excluded by the original 12.4.1 conjugator and the
12.4.9 reciprocal-commutator obstruction.  Its numerical parameter bound is
proved from the original hyperplane centralizers.  Thus the Chapter 13 row
sieve retains precisely the independent Sylow-normalizer and 12.4.8 source
inputs, with the literal chosen module and its quotient marking.

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

/-- Supply the exact G₂ callback of the guarded L₃/G₂ row sieve. -/
theorem fixedSpaceRows1332At_of_guarded_hyperplanes
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
    (normalizers : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      normalizer (T : Set G) ≤ normalizer (K : Set G))
    (hyperplanes : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      ∀ U ≤ W, ChapterE.subgroupCorank W U = 1 →
        centralizer (U : Set G) ≤ normalizer (W : Set G)) :
    FixedSpaceRows1332At (T := T) := by
  apply fixedSpaceRows1332At_of_l3_source h1331 hmany structural modules exits
  intro K W hK D hne E
  apply g2_fixed_of_guarded_hyperplanes h1331.hypothesis1311 hK D structural
    modules hmany (exits K) E (normalizers K W hK D hne E)
  intro _
  exact hyperplanes K W hK D hne E

/-- The original 13.3.2 module conclusion from the two independent G₂
source families.  No fixed-space callback remains. -/
theorem originalFixedModule1332At_of_guarded_hyperplanes
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
    (normalizers : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      normalizer (T : Set G) ≤ normalizer (K : Set G))
    (hyperplanes : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      ∀ U ≤ W, ChapterE.subgroupCorank W U = 1 →
        centralizer (U : Set G) ≤ normalizer (W : Set G)) :
    OriginalFixedModule1332At T L := by
  exact originalFixedModule1332At_of_fixed_space_rows h1331 hmany quasisimple models
    structural modules
    (fixedSpaceRows1332At_of_guarded_hyperplanes h1331 hmany structural modules exits
      normalizers hyperplanes)

/-! The completed moved-family detector discharges the normalizer premise
needed by the G₂ endgame.  The only remaining source callback here is the
independent 12.4.8 hyperplane-centralizer inclusion. -/

theorem fixedSpaceRows1332At_of_guarded_hyperplanes_source
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
    (hyperplanes : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      ∀ U ≤ W, ChapterE.subgroupCorank W U = 1 →
        centralizer (U : Set G) ≤ normalizer (W : Set G)) :
    FixedSpaceRows1332At (T := T) := by
  apply fixedSpaceRows1332At_of_guarded_hyperplanes h1331 hmany structural modules exits
  · intro K W hK D hne E
    exact Chapter12.Section04.SmallFusion.G2Source.sylow_normalizer_le_of_g2_weyl_source
      hK D structural E hne
  · exact hyperplanes

theorem originalFixedModule1332At_of_guarded_hyperplanes_source
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
    (hyperplanes : ∀ (K W : Subgroup G),
      Hypothesis1223 KnownSimple.IsKnownSimple T K →
      (D : ChosenModule T K W) →
      W ⊓ centralizer (K : Set G) ≠ ⊥ →
      ActionEquiv D.quotientAction
        (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)) →
      ∀ U ≤ W, ChapterE.subgroupCorank W U = 1 →
        centralizer (U : Set G) ≤ normalizer (W : Set G)) :
    OriginalFixedModule1332At T L := by
  exact originalFixedModule1332At_of_fixed_space_rows h1331 hmany quasisimple models
    structural modules
    (fixedSpaceRows1332At_of_guarded_hyperplanes_source h1331 hmany structural
      modules exits hyperplanes)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
