module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock0
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock1
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock2
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock3
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock4
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock5
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock6
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairBlock7

/-!
# A block of the exhaustive scalar-pair certificate

Each row fixes one scalar quadratic code of weight ten and checks all 168
possible partner codes. When their truth tables cover the fifteen nonzero
vectors, the reconstructed coefficient code must occur in the witness list.
All checks use kernel reduction. Splitting the rows bounds checking cost.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

private theorem scalar_pairs_checks : (scalarCandidates.all scalarRowCheck) = true := by
  have hl : scalarCandidates = scalarPairBlock0 ++ scalarPairBlock1 ++ scalarPairBlock2 ++ scalarPairBlock3 ++ scalarPairBlock4 ++ scalarPairBlock5 ++ scalarPairBlock6 ++ scalarPairBlock7 := by rfl
  rw [hl]
  simp only [List.all_append, scalar_pair_block_0, scalar_pair_block_1, scalar_pair_block_2, scalar_pair_block_3, scalar_pair_block_4, scalar_pair_block_5, scalar_pair_block_6, scalar_pair_block_7,
    Bool.and_true]

public theorem scalar_pairs_cover : ∀ a : Fin 1024, a ∈ scalarCandidates →
    ∀ b : Fin 1024, b ∈ scalarCandidates →
    (scalarTable a ||| scalarTable b) = 65534#16 →
    (unitaryWitnesses.any fun r => decide (r.1 = pairedCode a b)) = true := by
  intro a ha b hb hu
  have hrow := List.all_eq_true.mp scalar_pairs_checks a ha
  have hp := List.all_eq_true.mp hrow b hb
  simpa only [if_pos hu] using hp

end MacWilliamsSylow.QuadraticCertificate

