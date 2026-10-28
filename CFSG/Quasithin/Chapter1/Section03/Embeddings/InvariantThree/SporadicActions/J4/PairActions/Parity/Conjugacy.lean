module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.Max1Exclusion

/-!
# Conjugacy of max4-type Sylow overgroups: conditional assembly

The checked max1 exclusion removes one branch of the complete overgroup
cover. With the max4 quotient and the remaining centralizer exclusion,
`eq_conjugate` identifies each actual max4-type subgroup as a conjugate of
the literal ATLAS subgroup. Composing these two conjugations gives the
conjugator required by `MaximalFourSylowConjugacy`.

This does not yet prove `maximalFourSylowConjugacy`: its three explicit
model inputs must still be discharged. No normalizer, pair-coverage, or
automorphism-lift premise occurs. See `Conjugacy.Reduction` for the source
list and the distinction from the book's application on printed p.511.
-/

public section

open Subgroup Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

open Max4Conjugacy

/-- Conditional assembly over all actual max4-type Sylow overgroups.
The quotient, exhaustive cover, and involution-centralizer exclusion remain
separate model obligations. -/
theorem maximalFourSylowConjugacy_of_overgroupCover
    (hQ : MaximalFourQuotient) (hcover : ProperSylowOvergroupCover)
    (h2 : InvolutionCentralizerOmitsThirtyFive) :
    MaximalFourSylowConjugacy := by
  intro _ _ _ S M N hSM hSN hM hN
  obtain ⟨g, hg⟩ := eq_conjugate hQ hcover max1_orderOf_ne_thirtyFive h2 S M hSM hM
  obtain ⟨h, hh⟩ := eq_conjugate hQ hcover max1_orderOf_ne_thirtyFive h2 S N hSN hN
  refine ⟨h * g⁻¹, ?_⟩
  rw [hg, map_map]
  have hc : (MulAut.conj (h * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj h).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc]
  exact hh.symm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
