module

public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.PairCandidates
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.FusionConstraints
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.FusionElimination.Transfer
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.FusionElimination.CandidateCheck

/-!
# Eliminating Tits Sylow image pairs by both parabolic conjugacies

The two genuine internal conjugacy conditions preserve two certified labels.
On the 8192 candidate image pairs, equality of these labels forces membership
in the published 2048-entry mask. The label proofs use only the actual Sylow
subgroup, its two generators, and the five- and three-coset parabolic covers.
No two-core description or exhaustion of Sylow automorphisms is assumed.

Source: the Atlas realization of Parrott (1972), §5, p.683. The finite data
are reproducible with `FusionElimination/source/generate_certificate.py`;
every computational transfer is checked by the Lean kernel.
-/

namespace Tits.SharpOuterBound.LocalImageBound
open FusionElimination

/-- Both actual parabolic conjugacies eliminate every candidate outside the mask. -/
public theorem candidatePair_allowed_of_fusion (i : Fin 8192)
    (hfirst : FirstFusionCondition (candidatePair i))
    (hsecond : SecondFusionCondition (candidatePair i)) : allowedIndex i = true := by
  apply mask_check i
  · have h := first_label_isConj (pairEvaluation (candidatePair i) 37)
      (pairEvaluation (candidatePair i) 260) hfirst
    simpa only [sylowLabel, sylowPerm_pairEvaluation, evaluatedCoordinate_eq,
      fastCandidatePair_eq] using h
  · have h := second_label_isConj (pairEvaluation (candidatePair i) 4)
      (pairEvaluation (candidatePair i) 260) hsecond
    simpa only [sylowLabel, sylowPerm_pairEvaluation, evaluatedCoordinate_eq,
      fastCandidatePair_eq] using h

end Tits.SharpOuterBound.LocalImageBound
