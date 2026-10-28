module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedFourOddNormalizers

/-!
# Excluding the original doubled-natural branches

The original degree-four marked point theorem supplies the last marked omega
input in the doubled-branch exclusion. The existing original nonsingular,
odd-normalizer, fixed-space and weak-closure producers supply its other
inputs. Both source degrees are therefore excluded from the literal chosen
module under the original multiple-maximal-overgroup hypothesis.
Source: Aschbacher--Smith 12.1.11, printed pp.793--794.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original degree-four doubled-natural exclusion with its marked point
input constructed from the same source. -/
theorem doubleNatural_four_excluded_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) : False := by
  exact D.doubleNatural_four_excluded_of_many_of_omega_fixed h hmany B
    (D.doubleNatural_four_markedOmegaFixed_of_many h hmany B)

/-- Both original doubled-natural degrees are excluded without a marked
omega, weak-closure, odd-normalizer or nonsingular-centralizer premise. -/
theorem doubleNatural_excluded_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) : False := by
  rcases B.degree with rfl | rfl
  · exact D.doubleNatural_four_excluded_of_many h hmany B
  · exact D.doubleNatural_five_excluded_of_many h hmany B

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
