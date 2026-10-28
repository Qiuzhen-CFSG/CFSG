module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation

/-!
# The conjugation route to excluding large radical J₄ quotient subgroups

The kernel and image of the ambient conjugation map provide independent
inputs to the remaining normalizer calculation. Their three-part bounds
imply the exact quotient exclusion used by the extraspecial pair reduction.
Both model bounds remain explicit; the unconditional exclusion is not
asserted here.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher (1986).
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Assemble the original quotient contract from the two concrete
conjugation bounds. Their construction remains a separate obligation. -/
theorem fixedTwoLargeNormalizerQuotientExclusion_of_conjugation
    (hcentral : FixedTwoLargeCentralizerThreeFree)
    (haction : FixedTwoLargeConjugationThreePartBound) :
    FixedTwoLargeNormalizerQuotientExclusion := by
  intro _ _ _ S hS K hKT hSN hindex hrad L _ _
  exact fixedTwoLargeNormalizerQuotient_card_ne_of_conjugation
    (hcentral S hS K hKT hSN hindex hrad)
    (haction S hS K hKT hSN hindex hrad) L _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
