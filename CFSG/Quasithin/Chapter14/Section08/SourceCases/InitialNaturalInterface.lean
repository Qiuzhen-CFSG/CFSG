module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalPredecessorInterface
public import CFSG.Quasithin.Chapter13.Section01.SourceHypotheses
public import CFSG.Quasithin.Chapter12.Section09.SourceSetup
import CFSG.Quasithin.Chapter12.Section09.SourceAt.LargerLinear

/-!
# Larger-linear exclusion from the remaining initial natural marking

The original Section09 argument uses structure and modules at this same
G,T. Its internal degree-four constituent and degree-five natural marking
are supplied by their source proofs. Only the initial degree-four chosen
module marking remains explicit. The original ambient exclusions are
retained in Hypothesis1311.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02 Chapter12.Section09 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Exclude the actual larger linear quotients under the original ambient
exclusions, with only the initial degree-four natural marking outstanding. -/
theorem larger_linear_of_initial_natural
    (h : Hypothesis1311 T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (four : ∀ L V : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2 →
      NaturalModule D 4) :
    ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (Chapter1.XiQuotient I) n 2 := by
  intro I hi n hn
  exact Chapter13.Section03.SourceClassification.largerLinear_excluded_of_local_source
    h structural modules hmany four hi hn

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
