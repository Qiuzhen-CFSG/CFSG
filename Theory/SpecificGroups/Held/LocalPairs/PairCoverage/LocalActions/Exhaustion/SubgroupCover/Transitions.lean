module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Transitions.Local0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Transitions.Local1

/-!
# Certified positive Held right-coset transitions

All 540 published positive transitions hold in the actual Held carrier.
Point evaluation uses existing certified packed permutations, and equality
follows from the four-point base. `doubleCosetCoverage_of_transitions` can now
consume this unconditional certificate; no local index or order is assumed.

Sources: ATLAS HeG1-p2058B0 and max3W1/max4W1; GLS3 Table 5.3p;
Aschbacher–Smith, pp.509–511. The exact factor words and conventions are retained
in `SubgroupCover/source`. No additional premise is introduced here.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover

/-- The two positive generators have every published right-coset transition. -/
public theorem positiveTransitions : PositiveTransitions := by
  intro i r k
  apply TransitionChecks.transition_of_pointCheck
  cases i
  · exact TransitionChecks.checks_false r k
  · exact TransitionChecks.checks_true r k

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
