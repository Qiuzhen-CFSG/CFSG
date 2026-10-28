module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts

/-!
# Literal comparison data for the Held residual-nine calculation

The pure pair is the unchanged candidate product (false, 0). We publish a
short word proposed for conjugating the full representative normalizer to
this pair, together with the small target for its quotient map. These are
definitions only: the comparison equality and the quotient map still need
independent proofs.

The word was found using the original ATLAS degree-2058 permutations, with
the existing convention that inverts GAP permutations to obtain Lean's
left action. Source context: GLS3 Table 5.3p and Aschbacher--Smith, p.526.
In particular this comparison concerns the join of both E64 seeds.
-/

@[expose] public section
namespace Held.AutomorphismLocalPair.ResidualNine

/-- The proposed map from the representative normalizer to the pure pair is conjugation
by this literal word. No comparison equality is asserted by the definition. -/
def pairConjugator : He :=
  LocalPairs.PairCoverage.LocalActions.evalLocalWord false
    [(true, -2), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1),
      (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)]

/-- The precise finite target of the required pair quotient map. -/
abbrev QuotientModel := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

end Held.AutomorphismLocalPair.ResidualNine
