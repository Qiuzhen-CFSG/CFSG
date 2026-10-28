module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.Stabilizers
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.LowerBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower

/-!
# The two Held rank-six ambient normalizers

The fixed-point calculations identify a sextet for each of the literal rows
20 and 21. Every ambient normalizer preserves this sextet. Graph preservation
bounds its entire stabilizer by 138240. Each specified conjugated candidate
already lies in the normalizer, and its order is at least 138240. Consequently
the normalizer, sextet stabilizer, and specified candidate are equal.

The only premises are that the fixed representative is a two-group and that
Held preserves the published graph. In particular, no pair-stabilizer bound,
ambient order, maximality, coverage, or classification hypothesis is needed.
Source: GLS3 Table 5.3p, the literal ATLAS max3/max4 programs, and condition E
in Aschbacher–Smith, printed pp.3–4 and 481–482.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Subgroup LocalPairs.SylowGeometry.Calculations
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient

/-- The unchanged catalogue index for each of the two rank-six rows. -/
@[expose] def index (k : Fin 2) : Fin 5 := if k = 0 then 3 else 4

/-- The exact max4 or max3 conjugate specified by the original catalogue. -/
@[expose] def candidateGroup (k : Fin 2) : Subgroup He :=
  (subgroup (candidate (index k))).map (MulAut.conj (conjugator (index k))).toMonoidHom

theorem candidateGroup_le_normalizer (k : Fin 2) :
    candidateGroup k ≤ normalizer (ambient (row k) : Set He) := by
  fin_cases k
  · exact conjugated_candidate_le_normalizer 3
  · exact conjugated_candidate_le_normalizer 4

theorem candidateGroup_card_ge (hp : IsPGroup 2 representative) (k : Fin 2) :
    138240 ≤ Nat.card (candidateGroup k) := by
  rw [candidateGroup, card_map_of_injective (MulAut.conj _).injective]
  fin_cases k
  · exact max4_card_ge hp
  · exact Max3.local_card_ge_of_representative_orbits
      InnerNormalizer.orbitSizeLabel_eq_card_orbit

/-- Identification with an actual ambient stabilizer, with all finite premises proved. -/
theorem sextetStabilizer_eq_candidateGroup (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup) (k : Fin 2) :
    sextetStabilizer k = candidateGroup k := by
  exact (eq_of_le_of_card_ge
    ((candidateGroup_le_normalizer k).trans (normalizer_le_sextetStabilizer k))
    ((sextetStabilizer_card_le hgraph k).trans (candidateGroup_card_ge hp k))).symm

/-- The exact ambient normalizer identity for row 20 or row 21. -/
theorem normalizer_eq_candidateGroup (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup) (k : Fin 2) :
    normalizer (ambient (row k) : Set He) = candidateGroup k := by
  apply le_antisymm _ (candidateGroup_le_normalizer k)
  rw [← sextetStabilizer_eq_candidateGroup hp hgraph]
  exact normalizer_le_sextetStabilizer k

/-- In these two rows the full fixed-sextet stabilizer normalizes the row itself. -/
theorem normalizer_eq_sextetStabilizer (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup) (k : Fin 2) :
    normalizer (ambient (row k) : Set He) = sextetStabilizer k := by
  rw [normalizer_eq_candidateGroup hp hgraph, sextetStabilizer_eq_candidateGroup hp hgraph]

/-- The required two ambient upper inclusions, with the published words and conjugators. -/
theorem normalizer_upper (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup)
    (k : Fin 5) (hk : 3 ≤ k.val) :
    normalizer (ambient (distinguished k) : Set He) ≤
      (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom := by
  fin_cases k
  · norm_num at hk
  · norm_num at hk
  · norm_num at hk
  · exact (normalizer_eq_candidateGroup hp hgraph 0).le
  · exact (normalizer_eq_candidateGroup hp hgraph 1).le

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
