module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage

/-!
# The two Held involution classes in the normalized-pair calculation

The existing exhaustive Sylow-word fusion theorem covers every involution by
`a` and `TwoLocalCandidates.max5First ^ 4`. The latter word is exactly
`(a * b ^ 3) ^ 4`, the second seed of the normalized-pair calculation. This
adapter identifies the literal representatives and converts the explicit inner
conjugators to `IsConj`; it adds no coverage or structural hypotheses.

Source: the checked ATLAS word and Sylow certificates in
`InvolutionFixedData.Inner.Coverage`. No legacy subgroup catalogue is used.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

/-- Every actual involution is in one of the two classes used by the pair tests. -/
public theorem involutionCoverage : InvolutionCoverage := by
  intro x hx
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage x hx with h | h
  · exact Or.inl (isConj_iff.mpr h)
  · exact Or.inr (isConj_iff.mpr h)

end Held.Realization.MarkedConjugacy.NormalizedPairs
