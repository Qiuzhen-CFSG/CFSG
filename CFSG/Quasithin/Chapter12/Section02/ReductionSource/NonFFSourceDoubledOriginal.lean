module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledRemainingThree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryExclusion

/-!
# The complete original marked non-FF doubled exclusion

Every constituent row is now discharged under the original chosen module,
Sylow subgroup and multiple-two-local-overgroup hypothesis. The previously
remaining nonbinary linear-three, alternating-six and alternating-seven rows
are excluded by their genuine original sources. No numerical or module-row
callback is retained.
Source: Aschbacher--Smith 7.1--7.7 and12.2.2, printed pp.696--707,795.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original non-FF marked doubled branch is impossible. -/
theorem sourceOrbit_markedDoubled_nonFF_excluded_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : False := by
  rcases D.sourceOrbit_nonFF_markedDoubled_remaining_three h hd hmany hnon with
    ⟨F,hn,hm⟩ | hm | ⟨σ,hσ,hm⟩
  · exact D.sourceOrbit_linear_excluded h hd hmany hnon F hn hm
  · exact hnon (D.sourceOrbit_six_ff h hd hmany hm)
  · exact D.sourceOrbit_seven_excluded h hd hmany hnon σ hσ hm

/-- The original marked doubled whole orbit is an FF-module. -/
theorem sourceOrbit_markedDoubled_FF_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hd : D.MarkedDoubled) : IsFFModule D.sourceOrbitNormalizerRepresentation := by
  by_contra hnon
  exact D.sourceOrbit_markedDoubled_nonFF_excluded_of_many h hmany hd hnon
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
