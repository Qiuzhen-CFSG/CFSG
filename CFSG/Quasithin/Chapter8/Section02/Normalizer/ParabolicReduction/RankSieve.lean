module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Basic

/-!
# The odd-rank and minimal-parabolic sieve in Lemma 8.2.9

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.720 (PDF p.737).

The common deductions are proved in `RankSieve.Basic`: generation by I and T,
triviality of the residual action on the literal local two-core quotient,
odd-rank comparisons with marked models, the pair-intersection dichotomy,
and the prime-residual applications of `ResidualLift`.

The full source sieve remains to be assembled here. Its independent M24
code/cocode and L3(4)/M22 branches must still derive the generation-parameter
bounds, instantiate the model facts, inspect the complete E.2.2/B.6.8 lists,
and discharge the remaining quotient covers. The code branch must prove
that H is a 3′-group; the bound m₃(H) ≤ 1 does not supply that assertion.
Neither the unitary nor chief-section exclusions are asserted by this module.
-/
