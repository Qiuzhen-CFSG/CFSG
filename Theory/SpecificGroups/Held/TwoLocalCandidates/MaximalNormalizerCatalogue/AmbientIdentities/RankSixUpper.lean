module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate

/-!
# Ambient normalizer bounds for the two Held rank-six rows

The literal rows 20 and 21 have six fixed vertices in the original Held action.
Their ambient normalizers preserve these sextets. The checked graph-stabilizer
bound is 138240, while each specified max4/max3 conjugate has order at least
138240 and lies in the corresponding normalizer. These inclusions and bounds
give the two ambient identities, retaining the published row-20 conjugator
and the identity conjugator for row 21.

This module exports the rank-six input for the five-normalizer assembly in
the catalogue namespace. The proof needs only the representative's two-group
property and preservation of the Held graph.

Source: GLS3 Table 5.3p and the literal ATLAS max3/max4 and catalogue words.
These are local model inputs for condition E in Aschbacher–Smith, printed
pp.3–4 and 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The ambient upper inclusions for row 20 into the specified max4 conjugate
and row 21 into max3. -/
public theorem normalizer_le_conjugated_candidate_of_rankSix
    (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup) :
    ∀ k : Fin 5, 3 ≤ k.val →
      normalizer (ambient (distinguished k) : Set He) ≤
        (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom :=
  RankSixCertificate.normalizer_upper hp hgraph

/-- The resulting ambient identities for the two literal elementary order-64 rows. -/
public theorem normalizer_eq_conjugated_candidate_of_rankSix
    (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup)
    (k : Fin 5) (hk : 3 ≤ k.val) :
    normalizer (ambient (distinguished k) : Set He) =
      (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom :=
  le_antisymm (normalizer_le_conjugated_candidate_of_rankSix hp hgraph k hk)
    (conjugated_candidate_le_normalizer k)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
