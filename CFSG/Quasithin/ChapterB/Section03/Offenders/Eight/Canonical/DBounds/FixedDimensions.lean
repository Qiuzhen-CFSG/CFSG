module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.DBounds.Transport
/-!
# Fixed spaces of the binary subgroup representatives

For the sixteen representatives under pair permutations, count fixed vectors in
the full module and core, and normalized constant-displacement vectors in the
deleted and natural modules. Normalization at the last coordinate is the proved
quotient equivalence from `Canonical.Dimensions`. In particular the full-support
cyclic subgroup has dimensions `(4, 4, 4, 4)`: its additional quotient fixed
vectors are retained. The vector-space cardinality formula gives exact dimensions.

These are computations in 256 binary vectors and the sixteen-element coordinate
group; no ambient symmetric-group enumeration is used.

Source: Aschbacher–Smith, Proposition B.3.2, printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
open Representation.BinaryOffender BinaryPermutation
def representativeRank : Fin 16 → ℕ := ![0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4]

def fullDim : Fin 16 → ℕ := ![8, 7, 6, 5, 4, 6, 5, 4, 5, 4, 4, 5, 4, 4, 4, 4]

def deletedDim : Fin 16 → ℕ := ![7, 6, 5, 4, 4, 5, 4, 3, 4, 3, 3, 4, 3, 3, 3, 3]

def coreDim : Fin 16 → ℕ := ![7, 6, 5, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]

def naturalDim : Fin 16 → ℕ := ![6, 5, 4, 3, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

theorem rank_representative (j : Fin 16) :
    rank (group (representative j)) = representativeRank j := by
  rw [rank, card_group]
  revert j
  decide +kernel

set_option maxRecDepth 4096 in
theorem dimensions_representative (j : Fin 16) :
    HasDimensions (group (representative j)) (fullDim j) (deletedDim j)
      (coreDim j) (naturalDim j) := by
  rw [group_eq_closure]
  apply dimensions
  · rw [count_bits]; revert j; decide +kernel
  · rw [count_bits]; revert j; decide +kernel
  · rw [count_bits]; revert j; decide +kernel
  · rw [count_bits]; revert j; decide +kernel

end CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
