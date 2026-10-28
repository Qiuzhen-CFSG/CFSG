module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 47

The tables give an exhaustive word list, generator transitions, normalizer
conjugation, and involution/square displacements. Kernel reduction checks all
identities in the concrete Sylow model. The certificate soundness theorem
puts the outside normalizer action in the automorphism two-core.

Source: Shinoda (1975), (2.3), pp. 81–82, for the root convention; the
representative is fixed in SmallEvenCandidates. Exploratory GAP tables supply
only proposed words: no externally computed group property is assumed.
-/

set_option Elab.async false

namespace ReeTwo.SylowModel
open Subgroup

-- Candidate 47, diagnostic label 803.
private def gen47 : Fin 5 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9]
private def cert47 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8,
    root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9, root 0 * root 3 * root 5 * root 6 * root 7 * root 8 * root 9,
    root 0 * root 2 * root 4 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9,
    root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9,
    root 2 * root 3 * root 4 * root 8 * root 9, root 5 * root 6 * root 8, root 5 * root 6 * root 7 * root 8,
    root 7, root 0 * root 3, root 0 * root 3 * root 5 * root 6 * root 8, root 0 * root 3 * root 5 * root 6 * root 7 * root 8,
    root 0 * root 2 * root 4 * root 7, root 0 * root 2 * root 4, root 0 * root 2 * root 4 * root 5 * root 6 * root 8,
    root 2 * root 3 * root 4 * root 5 * root 6, root 2 * root 3 * root 4 * root 5 * root 6 * root 7, root 2 * root 3 * root 4 * root 7 * root 8,
    root 5 * root 6 * root 8 * root 9, root 0 * root 3 * root 7 * root 9, root 0 * root 3 * root 9, root 0 * root 3 * root 5 * root 6 * root 8 * root 9,
    root 0 * root 2 * root 4 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, root 0 * root 3 * root 7]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 3],
    [2, 4], [3, 4], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [1, 2, 3], [1, 2, 4],
    [1, 3, 4], [2, 3, 4], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4]]
  base := 0
  next := fun i a => (![![1, 3, 6, 7, 8, 9, 10, 0, 13, 14, 16, 17, 18, 19, 20, 21, 2, 22, 23, 4, 5, 25, 26, 27, 28, 29, 11, 12, 30, 15, 31, 24],
      ![2, 6, 4, 10, 11, 12, 8, 16, 17, 18, 13, 0, 15, 22, 23, 24, 19, 1, 21, 26, 27, 28, 3, 25, 5, 30, 7, 29, 9, 31, 14, 20],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  prev := fun i a => (![![7, 0, 16, 1, 19, 20, 2, 3, 4, 5, 6, 26, 27, 8, 9, 29, 10, 11, 12, 13, 14, 15, 17, 18, 31, 21, 22, 23, 24, 25, 28, 30],
      ![11, 17, 0, 22, 2, 24, 1, 26, 6, 28, 3, 4, 5, 10, 30, 12, 7, 8, 9, 16, 31, 18, 13, 14, 15, 23, 19, 20, 21, 27, 25, 29],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  outside := root 2 * root 3 * root 4 * root 7
  conj := ![0, 9, 2, 3, 4, 5, 18, 20, 21, 1, 10, 11, 12, 13, 14, 15, 27, 28, 6, 29, 7, 8, 22, 23, 24, 25, 31, 16, 17, 19, 30, 26]
  unconj := ![0, 9, 2, 3, 4, 5, 18, 20, 21, 1, 10, 11, 12, 13, 14, 15, 27, 28, 6, 29, 7, 8, 22, 23, 24, 25, 31, 16, 17, 19, 30, 26]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid47 : cert47.Valid gen47 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq47 : Subgroup.closure (Set.range gen47) = smallEvenCandidate 47 := by
  change Subgroup.closure (Set.range gen47) = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen47, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate47_hasPCoreNormalizerWitness : (smallEvenCandidate 47).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq47]
  exact cert47.sound (IsPGroup.of_card (n := 12) card) gen47 valid47


end ReeTwo.SylowModel
