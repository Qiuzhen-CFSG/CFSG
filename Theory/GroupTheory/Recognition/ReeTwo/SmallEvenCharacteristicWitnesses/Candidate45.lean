module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 45

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

-- Candidate 45, diagnostic label 675.
private def gen45 : Fin 6 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def cert45 : InvolutionSquareCertificate SylowModel 6 64 where
  rep := ![1, root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9,
    root 8, rootOne ^ 2 * root 3, root 3 * root 4 * root 7 * root 8, root 3 * root 7 * root 9, root 3 * root 8 * root 9,
    root 3 * root 9, rootOne ^ 2 * root 4 * root 7 * root 8, rootOne ^ 2 * root 7 * root 9, rootOne ^ 2 * root 8 * root 9,
    rootOne ^ 2 * root 9, root 4 * root 8 * root 9, root 4 * root 7 * root 9, root 4 * root 7 * root 8 * root 9,
    root 7 * root 8, root 7, root 3 * root 8, rootOne ^ 2 * root 8, root 4 * root 7, root 7 * root 8 * root 9,
    rootOne ^ 2 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 3 * root 7 * root 9, rootOne ^ 2 * root 3 * root 8 * root 9,
    rootOne ^ 2 * root 3 * root 9, root 3 * root 4 * root 8 * root 9, root 3 * root 4 * root 7 * root 9, root 3 * root 4 * root 7 * root 8 * root 9,
    root 3 * root 7 * root 8, root 3 * root 7, rootOne ^ 2 * root 4 * root 8 * root 9, rootOne ^ 2 * root 4 * root 7 * root 9,
    rootOne ^ 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 7 * root 8, rootOne ^ 2 * root 7,
    root 4, root 4 * root 8, rootOne ^ 2 * root 3 * root 8, root 3 * root 4 * root 7, root 3 * root 7 * root 8 * root 9,
    rootOne ^ 2 * root 4 * root 7, rootOne ^ 2 * root 7 * root 8 * root 9, root 4 * root 9, rootOne ^ 2 * root 3 * root 4 * root 8 * root 9,
    rootOne ^ 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 3 * root 4 * root 7 * root 8 * root 9,
    rootOne ^ 2 * root 3 * root 7 * root 8, rootOne ^ 2 * root 3 * root 7, root 3 * root 4, root 3 * root 4 * root 8,
    rootOne ^ 2 * root 4, rootOne ^ 2 * root 4 * root 8, rootOne ^ 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 3 * root 7 * root 8 * root 9,
    root 3 * root 4 * root 9, rootOne ^ 2 * root 4 * root 9, rootOne ^ 2 * root 3 * root 4, rootOne ^ 2 * root 3 * root 4 * root 8,
    rootOne ^ 2 * root 3 * root 4 * root 9]
  words := ![[], [0], [1], [2], [3], [4], [5], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [1, 2],
    [1, 3], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 0, 3],
    [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 1, 5], [0, 2, 3], [0, 2, 4], [0, 2, 5], [0, 3, 4], [0, 3, 5], [1, 2, 3],
    [1, 2, 4], [1, 2, 5], [1, 3, 4], [1, 3, 5], [2, 3, 4], [2, 3, 5], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 0, 3],
    [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 2, 3], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5], [0, 1, 3, 4], [0, 1, 3, 5],
    [0, 2, 3, 4], [0, 2, 3, 5], [1, 2, 3, 4], [1, 2, 3, 5], [0, 0, 0, 1, 2], [0, 0, 0, 1, 3], [0, 0, 0, 2, 3],
    [0, 0, 1, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 5], [0, 0, 0, 1, 2, 3]]
  base := 0
  next := fun i a => (![![1, 7, 8, 9, 10, 11, 12, 22, 23, 24, 25, 6, 5, 26, 27, 28, 29, 30, 31, 32, 33, 34, 0, 42, 43, 44, 45, 46, 16, 15, 47, 19, 18, 21, 20, 48, 49, 50, 51, 52, 53, 54, 2, 3, 4, 57, 58, 59, 60, 37, 36, 39, 38, 41, 40, 61, 62, 13, 14, 17, 63, 56, 55, 35],
      ![2, 8, 0, 13, 14, 15, 16, 23, 1, 26, 27, 28, 29, 3, 4, 5, 6, 35, 36, 37, 38, 39, 42, 7, 45, 46, 9, 10, 11, 12, 48, 49, 50, 51, 52, 17, 18, 19, 20, 21, 55, 56, 22, 57, 58, 24, 25, 60, 30, 31, 32, 33, 34, 61, 62, 40, 41, 43, 44, 63, 47, 53, 54, 59],
      ![3, 9, 13, 0, 17, 18, 19, 24, 26, 1, 30, 31, 32, 2, 35, 36, 37, 4, 5, 6, 40, 41, 43, 45, 7, 47, 8, 48, 49, 50, 10, 11, 12, 53, 54, 14, 15, 16, 55, 56, 20, 21, 57, 22, 59, 23, 60, 25, 27, 28, 29, 61, 62, 33, 34, 38, 39, 42, 63, 44, 46, 51, 52, 58],
      ![4, 10, 14, 17, 0, 20, 21, 25, 27, 30, 1, 33, 34, 35, 2, 38, 39, 3, 40, 41, 5, 6, 44, 46, 47, 7, 48, 8, 51, 52, 9, 53, 54, 11, 12, 13, 55, 56, 15, 16, 18, 19, 58, 59, 22, 60, 23, 24, 26, 61, 62, 28, 29, 31, 32, 36, 37, 63, 42, 43, 45, 49, 50, 57],
      ![5, 11, 15, 18, 20, 0, 7, 6, 28, 31, 33, 1, 22, 36, 38, 2, 23, 40, 3, 24, 4, 25, 12, 16, 19, 21, 49, 51, 8, 42, 53, 9, 43, 10, 44, 55, 13, 45, 14, 46, 17, 47, 29, 32, 34, 37, 39, 41, 61, 26, 57, 27, 58, 30, 59, 35, 60, 50, 52, 54, 56, 48, 63, 62],
      ![6, 12, 16, 19, 21, 7, 0, 5, 29, 32, 34, 22, 1, 37, 39, 23, 2, 41, 24, 3, 25, 4, 11, 15, 18, 20, 50, 52, 42, 8, 54, 43, 9, 44, 10, 56, 45, 13, 46, 14, 47, 17, 28, 31, 33, 36, 38, 40, 62, 57, 26, 58, 27, 59, 30, 60, 35, 49, 51, 53, 55, 63, 48, 61]]) i a
  prev := fun i a => (![![22, 0, 42, 43, 44, 12, 11, 1, 2, 3, 4, 5, 6, 57, 58, 29, 28, 59, 32, 31, 34, 33, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 20, 21, 63, 50, 49, 52, 51, 54, 53, 23, 24, 25, 26, 27, 30, 35, 36, 37, 38, 39, 40, 41, 62, 61, 45, 46, 47, 48, 55, 56, 60],
      ![2, 8, 0, 13, 14, 15, 16, 23, 1, 26, 27, 28, 29, 3, 4, 5, 6, 35, 36, 37, 38, 39, 42, 7, 45, 46, 9, 10, 11, 12, 48, 49, 50, 51, 52, 17, 18, 19, 20, 21, 55, 56, 22, 57, 58, 24, 25, 60, 30, 31, 32, 33, 34, 61, 62, 40, 41, 43, 44, 63, 47, 53, 54, 59],
      ![3, 9, 13, 0, 17, 18, 19, 24, 26, 1, 30, 31, 32, 2, 35, 36, 37, 4, 5, 6, 40, 41, 43, 45, 7, 47, 8, 48, 49, 50, 10, 11, 12, 53, 54, 14, 15, 16, 55, 56, 20, 21, 57, 22, 59, 23, 60, 25, 27, 28, 29, 61, 62, 33, 34, 38, 39, 42, 63, 44, 46, 51, 52, 58],
      ![4, 10, 14, 17, 0, 20, 21, 25, 27, 30, 1, 33, 34, 35, 2, 38, 39, 3, 40, 41, 5, 6, 44, 46, 47, 7, 48, 8, 51, 52, 9, 53, 54, 11, 12, 13, 55, 56, 15, 16, 18, 19, 58, 59, 22, 60, 23, 24, 26, 61, 62, 28, 29, 31, 32, 36, 37, 63, 42, 43, 45, 49, 50, 57],
      ![5, 11, 15, 18, 20, 0, 7, 6, 28, 31, 33, 1, 22, 36, 38, 2, 23, 40, 3, 24, 4, 25, 12, 16, 19, 21, 49, 51, 8, 42, 53, 9, 43, 10, 44, 55, 13, 45, 14, 46, 17, 47, 29, 32, 34, 37, 39, 41, 61, 26, 57, 27, 58, 30, 59, 35, 60, 50, 52, 54, 56, 48, 63, 62],
      ![6, 12, 16, 19, 21, 7, 0, 5, 29, 32, 34, 22, 1, 37, 39, 23, 2, 41, 24, 3, 25, 4, 11, 15, 18, 20, 50, 52, 42, 8, 54, 43, 9, 44, 10, 56, 45, 13, 46, 14, 47, 17, 28, 31, 33, 36, 38, 40, 62, 57, 26, 58, 27, 59, 30, 60, 35, 49, 51, 53, 55, 63, 48, 61]]) i a
  outside := rootOne * rootOne ^ 2
  conj := ![0, 53, 2, 24, 25, 5, 6, 7, 61, 34, 32, 30, 59, 45, 46, 15, 16, 17, 19, 18, 21, 20, 54, 23, 3, 4, 52, 50, 48, 63, 11, 44, 10, 43, 9, 35, 37, 36, 39, 38, 40, 41, 62, 33, 31, 13, 14, 47, 28, 58, 27, 57, 26, 1, 22, 55, 56, 51, 49, 12, 60, 8, 42, 29]
  unconj := ![0, 53, 2, 24, 25, 5, 6, 7, 61, 34, 32, 30, 59, 45, 46, 15, 16, 17, 19, 18, 21, 20, 54, 23, 3, 4, 52, 50, 48, 63, 11, 44, 10, 43, 9, 35, 37, 36, 39, 38, 40, 41, 62, 33, 31, 13, 14, 47, 28, 58, 27, 57, 26, 1, 22, 55, 56, 51, 49, 12, 60, 8, 42, 29]
  squareRoots := ![[], [], [], [1], [1], [], [], [], [], [], [], [], [], [1], [1], [], [], [], [1], [1],
    [1], [1], [], [], [1], [1], [], [], [], [], [], [], [], [], [], [], [1], [1], [1], [1], [], [], [], [],
    [], [1], [1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid45 : cert45.Valid gen45 := by decide +kernel
private theorem gen_eq45 : Subgroup.closure (Set.range gen45) = smallEvenCandidate 45 := by
  change Subgroup.closure (Set.range gen45) = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen45, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate45_hasPCoreNormalizerWitness : (smallEvenCandidate 45).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq45]
  exact cert45.sound (IsPGroup.of_card (n := 12) card) gen45 valid45


end ReeTwo.SylowModel
