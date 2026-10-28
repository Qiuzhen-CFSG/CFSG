module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Actor0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Coordinates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair00.Alphabet

/-!
# Preservation and marked basis formulas for pure Held actor 0

The tables are evaluation aids; their identities are checked on every
one of the 2058 letters by Lean kernel reduction. The ambient word uses
only Held's two generators and the already certified ATLAS outer implementer.
Source: the unchanged HeG1-p2058B0 carrier, HeG1-a2W1, GLS3 Table 5.3p,
and quasithin pp.509–511. See source/README.md for the discovery provenance.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
set_option maxRecDepth 8192

namespace Actor0
open Subgroup

@[expose] public def twoImageWord : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(3, 1), (2, 1), (1, 1), (3, 1), (2, 1), (1, 1), (3, 1), (2, 1), (1, 1), (3, 1), (2, 1), (0, 1)]
  | 1 => [(1, 1)]
  | 2 => [(2, 1), (1, 1), (2, 1), (3, 1), (2, 1), (1, 1), (2, 1)]
  | 3 => [(3, 1), (1, 1), (3, 1), (0, 1), (2, 1), (3, 1), (1, 1), (3, 1), (0, 1)]

private theorem two0_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2 =
    representation (twoGenerator false 0) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2_eq

private theorem two1_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3 =
    representation (twoGenerator false 1) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3_eq

private theorem two2_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4 =
    representation (twoGenerator false 2) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4_eq

private theorem two3_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5 =
    representation (twoGenerator false 3) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5_eq

set_option maxHeartbeats 2400000 in
private theorem conj_two0 :
    perm * representation (twoGenerator false 0) * perm⁻¹ =
      representation (evalTwo false (twoImageWord 0)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two0_eq, ← two1_eq, ← two2_eq, ← two3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two1 :
    perm * representation (twoGenerator false 1) * perm⁻¹ =
      representation (evalTwo false (twoImageWord 1)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two2 :
    perm * representation (twoGenerator false 2) * perm⁻¹ =
      representation (evalTwo false (twoImageWord 2)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two1_eq, ← two2_eq, ← two3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two3 :
    perm * representation (twoGenerator false 3) * perm⁻¹ =
      representation (evalTwo false (twoImageWord 3)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two0_eq, ← two1_eq, ← two2_eq, ← two3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conj_two (k : Fin 4) :
    perm * representation (twoGenerator false k) * perm⁻¹ =
      representation (evalTwo false (twoImageWord k)) := by
  fin_cases k
  · exact conj_two0
  · exact conj_two1
  · exact conj_two2
  · exact conj_two3

set_option maxHeartbeats 2400000 in
private theorem conj_basis0 :
    perm * representation (basisGenerator false 0 0) * perm⁻¹ =
      representation (imageElement false 0) := by
  change perm * representation (oddGenerator false 0 0) * perm⁻¹ = representation (oddGenerator false 0 1 ^ (1 : ℤ))
  simp only [map_zpow, ← Pair00.odd0_eq, ← Pair00.odd1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_basis1 :
    perm * representation (basisGenerator false 0 1) * perm⁻¹ =
      representation (imageElement false 1) := by
  change perm * representation (oddGenerator false 0 1) * perm⁻¹ = representation (oddGenerator false 0 0 ^ (-1 : ℤ))
  simp only [map_zpow, ← Pair00.odd0_eq, ← Pair00.odd1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conj_basis (k : Fin 2) :
    perm * representation (basisGenerator false 0 k) * perm⁻¹ =
      representation (imageElement false k) := by
  fin_cases k
  · exact conj_basis0
  · exact conj_basis1

public theorem perm_normalizes_two :
    perm ∈ normalizer ((candidateTwo false 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  apply normalizes_generated (twoGenerator false)
  intro k
  rw [conj_two]
  exact ⟨evalTwo false (twoImageWord k), evalTwo_mem _ _, rfl⟩

public theorem perm_normalizes_odd :
    perm ∈ normalizer ((candidateOdd false 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  rw [← basis_closure false]
  apply normalizes_generated
  intro k
  rw [conj_basis, basis_closure]
  exact ⟨imageElement false k, imageElement_mem _ _, rfl⟩

end Actor0
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
