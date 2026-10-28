module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Actor1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors.Coordinates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair10.Alphabet

/-!
# Preservation and marked basis formulas for pure Held actor 1

The tables are evaluation aids; their identities are checked on every
one of the 2058 letters by Lean kernel reduction. The ambient word uses
only Held's two generators and the already certified ATLAS outer implementer.
Source: the unchanged HeG1-p2058B0 carrier, HeG1-a2W1, GLS3 Table 5.3p,
and quasithin pp.509–511. See source/README.md for the discovery provenance.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
set_option maxRecDepth 8192

namespace Actor1
open Subgroup

@[expose] public def twoImageWord : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(0, 1)]
  | 1 => [(1, 1), (0, 1)]
  | 2 => [(2, 1), (3, 1), (2, 1)]
  | 3 => [(3, 1), (0, 1), (2, 1), (0, 1), (3, 1)]

private theorem two0_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair2 =
    representation (twoGenerator true 0) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair2_eq

private theorem two1_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair3 =
    representation (twoGenerator true 1) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair3_eq

private theorem two2_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair4 =
    representation (twoGenerator true 2) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair4_eq

private theorem two3_eq : Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair5 =
    representation (twoGenerator true 3) := Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair5_eq

set_option maxHeartbeats 2400000 in
private theorem conj_two0 :
    perm * representation (twoGenerator true 0) * perm⁻¹ =
      representation (evalTwo true (twoImageWord 0)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two0_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two1 :
    perm * representation (twoGenerator true 1) * perm⁻¹ =
      representation (evalTwo true (twoImageWord 1)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two0_eq, ← two1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two2 :
    perm * representation (twoGenerator true 2) * perm⁻¹ =
      representation (evalTwo true (twoImageWord 2)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two2_eq, ← two3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_two3 :
    perm * representation (twoGenerator true 3) * perm⁻¹ =
      representation (evalTwo true (twoImageWord 3)) := by
  rw [representation_evalTwo]
  simp only [twoImageWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    ← two0_eq, ← two2_eq, ← two3_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conj_two (k : Fin 4) :
    perm * representation (twoGenerator true k) * perm⁻¹ =
      representation (evalTwo true (twoImageWord k)) := by
  fin_cases k
  · exact conj_two0
  · exact conj_two1
  · exact conj_two2
  · exact conj_two3

set_option maxHeartbeats 2400000 in
private theorem conj_basis0 :
    perm * representation (basisGenerator true 0 0) * perm⁻¹ =
      representation (imageElement true 0) := by
  change perm * representation (oddGenerator true 0 1) * perm⁻¹ = representation ((oddGenerator true 0 0 * oddGenerator true 0 1) ^ (-1 : ℤ))
  simp only [map_mul, map_zpow, ← Pair10.odd0_eq, ← Pair10.odd1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxHeartbeats 2400000 in
private theorem conj_basis1 :
    perm * representation (basisGenerator true 0 1) * perm⁻¹ =
      representation (imageElement true 1) := by
  change perm * representation (oddGenerator true 0 0 * oddGenerator true 0 1) * perm⁻¹ = representation (oddGenerator true 0 1 ^ (1 : ℤ))
  simp only [map_mul, map_zpow, ← Pair10.odd0_eq, ← Pair10.odd1_eq]
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conj_basis (k : Fin 2) :
    perm * representation (basisGenerator true 0 k) * perm⁻¹ =
      representation (imageElement true k) := by
  fin_cases k
  · exact conj_basis0
  · exact conj_basis1

public theorem perm_normalizes_two :
    perm ∈ normalizer ((candidateTwo true 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  apply normalizes_generated (twoGenerator true)
  intro k
  rw [conj_two]
  exact ⟨evalTwo true (twoImageWord k), evalTwo_mem _ _, rfl⟩

public theorem perm_normalizes_odd :
    perm ∈ normalizer ((candidateOdd true 0).map representation :
      Set (Equiv.Perm (Fin 2058))) := by
  rw [← basis_closure true]
  apply normalizes_generated
  intro k
  rw [conj_basis, basis_closure]
  exact ⟨imageElement true k, imageElement_mem _ _, rfl⟩

end Actor1
end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
