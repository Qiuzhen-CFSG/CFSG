module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.JoinBounds.Pair00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.JoinBounds.Pair01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.JoinBounds.Pair10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.JoinBounds.Pair11
import Mathlib.Tactic.FinCases

/-!
# Unconditional upper bounds for the four literal Held joins

In the faithful degree-2058 representation, each join is contained in a
certified cyclic-series closure with ten relative factors of two and two
of three. Relative powers, forward conjugates, tail support, and the six
original-generator expressions are all checked. Multiplying the cyclic
index bounds gives 9216, which transfers to the actual join by faithfulness.

The proof uses no factor-order hypothesis, global Held order, simplicity,
plane recognition, or normalizer computation. The parent order assembly
can combine this upper bound with the independently proved factor orders.

Sources: the unchanged ATLAS max3/max4 words and degree-2058 carrier;
LocalActions/source/Explore.g and Explore.txt; the proposed cyclic-series
data in CandidateOrders/source/pcdata.json. See JoinBounds/source/README.md
for the certificate architecture and reproduction instructions.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion

/-- A bound on the actual join of the unchanged odd and even candidate closures. -/
public theorem candidateProduct_card_le_9216 (i : Bool) (j : Fin 2) :
    Nat.card (candidateProduct i j) ≤ 9216 := by
  cases i
  · fin_cases j
    · exact JoinBounds.Pair00.bound
    · exact JoinBounds.Pair01.bound
  · fin_cases j
    · exact JoinBounds.Pair10.bound
    · exact JoinBounds.Pair11.bound

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
