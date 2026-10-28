module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 44

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

-- Candidate 44, diagnostic label 588.
private def gen44 : Fin 6 → SylowModel :=
  ![root 2 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def cert44 : InvolutionSquareCertificate SylowModel 6 64 where
  rep := ![1, root 2 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8,
    root 8 * root 9, root 9, root 2 * root 8 * root 9, root 2 * root 5 * root 6 * root 8, root 2 * root 6 * root 8,
    root 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 6 * root 7 * root 9, root 5 * root 6 * root 9,
    root 6 * root 9, root 6 * root 7, root 6 * root 7 * root 8, root 5, root 5 * root 7 * root 9, root 5 * root 7 * root 8 * root 9,
    root 7 * root 9, root 7 * root 8 * root 9, root 8, root 2 * root 5 * root 7 * root 9, root 2 * root 7 * root 9,
    root 2, root 2 * root 8, root 2 * root 5 * root 6 * root 7, root 2 * root 5 * root 6 * root 9, root 2 * root 5 * root 6 * root 8 * root 9,
    root 2 * root 6 * root 9, root 2 * root 6 * root 8 * root 9, root 2 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9,
    root 5 * root 6 * root 8, root 5 * root 6, root 6 * root 8, root 6, root 6 * root 7 * root 9, root 5 * root 8 * root 9,
    root 5 * root 9, root 5 * root 7, root 7, root 2 * root 5 * root 8 * root 9, root 2 * root 5 * root 7 * root 8,
    root 2 * root 5 * root 7, root 2 * root 7 * root 8, root 2 * root 7, root 2 * root 9, root 2 * root 5 * root 6 * root 7 * root 8 * root 9,
    root 2 * root 5 * root 6 * root 7 * root 9, root 2 * root 5 * root 6, root 2 * root 6, root 5 * root 6 * root 7,
    root 5 * root 6 * root 7 * root 8, root 5 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 5 * root 8,
    root 2 * root 5, root 2 * root 5 * root 8, root 2 * root 5 * root 7 * root 8 * root 9, root 2 * root 7 * root 8 * root 9,
    root 2 * root 5 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 9, root 2 * root 5 * root 9]
  words := ![[], [0], [1], [2], [3], [4], [5], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [1, 2], [1, 3],
    [1, 4], [1, 5], [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 1, 5],
    [0, 2, 3], [0, 2, 4], [0, 2, 5], [0, 3, 4], [0, 3, 5], [0, 4, 5], [1, 2, 3], [1, 2, 4], [1, 2, 5], [1, 3, 4],
    [1, 3, 5], [1, 4, 5], [2, 3, 4], [2, 3, 5], [2, 4, 5], [3, 4, 5], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5],
    [0, 1, 3, 4], [0, 1, 3, 5], [0, 1, 4, 5], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5], [0, 3, 4, 5], [1, 2, 3, 4],
    [1, 2, 3, 5], [1, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5], [0, 1, 2, 3, 4], [0, 1, 2, 3, 5], [0, 1, 2, 4, 5],
    [0, 1, 3, 4, 5], [0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]]
  base := 0
  next := fun i a => (![![1, 6, 7, 8, 9, 10, 11, 15, 18, 20, 21, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 36, 37, 2, 39, 40, 3, 41, 4, 5, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 53, 54, 12, 55, 13, 14, 56, 16, 17, 19, 57, 58, 59, 60, 61, 62, 32, 33, 35, 38, 63, 52],
      ![2, 7, 0, 12, 13, 14, 15, 1, 22, 23, 24, 25, 3, 4, 5, 6, 32, 33, 34, 35, 36, 37, 8, 9, 10, 11, 42, 43, 44, 45, 46, 47, 16, 17, 18, 19, 20, 21, 52, 53, 54, 55, 26, 27, 28, 29, 30, 31, 57, 58, 59, 60, 38, 39, 40, 41, 62, 48, 49, 50, 51, 63, 56, 61],
      ![3, 8, 12, 0, 16, 17, 18, 22, 1, 26, 27, 28, 2, 32, 33, 34, 4, 5, 6, 38, 39, 40, 7, 42, 43, 44, 9, 10, 11, 48, 49, 50, 13, 14, 15, 52, 53, 54, 19, 20, 21, 56, 23, 24, 25, 57, 58, 59, 29, 30, 31, 61, 35, 36, 37, 62, 41, 45, 46, 47, 63, 51, 55, 60],
      ![4, 9, 13, 16, 0, 19, 20, 23, 26, 1, 29, 30, 32, 2, 35, 36, 3, 38, 39, 5, 6, 41, 42, 7, 45, 46, 8, 48, 49, 10, 11, 51, 12, 52, 53, 14, 15, 55, 17, 18, 56, 21, 22, 57, 58, 24, 25, 60, 27, 28, 61, 31, 33, 34, 62, 37, 40, 43, 44, 63, 47, 50, 54, 59],
      ![5, 10, 14, 17, 19, 0, 21, 24, 27, 29, 1, 31, 33, 35, 2, 37, 38, 3, 40, 4, 41, 6, 43, 45, 7, 47, 48, 8, 50, 9, 51, 11, 52, 12, 54, 13, 55, 15, 16, 56, 18, 20, 57, 22, 59, 23, 60, 25, 26, 61, 28, 30, 32, 62, 34, 36, 39, 42, 63, 44, 46, 49, 53, 58],
      ![6, 11, 15, 18, 20, 21, 0, 25, 28, 30, 31, 1, 34, 36, 37, 2, 39, 40, 3, 41, 4, 5, 44, 46, 47, 7, 49, 50, 8, 51, 9, 10, 53, 54, 12, 55, 13, 14, 56, 16, 17, 19, 58, 59, 22, 60, 23, 24, 61, 26, 27, 29, 62, 32, 33, 35, 38, 63, 42, 43, 45, 48, 52, 57]]) i a
  prev := fun i a => (![![11, 0, 25, 28, 30, 31, 1, 2, 3, 4, 5, 6, 44, 46, 47, 7, 49, 50, 8, 51, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 58, 59, 22, 60, 23, 24, 61, 26, 27, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 63, 42, 43, 45, 48, 52, 53, 54, 55, 56, 57, 62],
      ![2, 7, 0, 12, 13, 14, 15, 1, 22, 23, 24, 25, 3, 4, 5, 6, 32, 33, 34, 35, 36, 37, 8, 9, 10, 11, 42, 43, 44, 45, 46, 47, 16, 17, 18, 19, 20, 21, 52, 53, 54, 55, 26, 27, 28, 29, 30, 31, 57, 58, 59, 60, 38, 39, 40, 41, 62, 48, 49, 50, 51, 63, 56, 61],
      ![3, 8, 12, 0, 16, 17, 18, 22, 1, 26, 27, 28, 2, 32, 33, 34, 4, 5, 6, 38, 39, 40, 7, 42, 43, 44, 9, 10, 11, 48, 49, 50, 13, 14, 15, 52, 53, 54, 19, 20, 21, 56, 23, 24, 25, 57, 58, 59, 29, 30, 31, 61, 35, 36, 37, 62, 41, 45, 46, 47, 63, 51, 55, 60],
      ![4, 9, 13, 16, 0, 19, 20, 23, 26, 1, 29, 30, 32, 2, 35, 36, 3, 38, 39, 5, 6, 41, 42, 7, 45, 46, 8, 48, 49, 10, 11, 51, 12, 52, 53, 14, 15, 55, 17, 18, 56, 21, 22, 57, 58, 24, 25, 60, 27, 28, 61, 31, 33, 34, 62, 37, 40, 43, 44, 63, 47, 50, 54, 59],
      ![5, 10, 14, 17, 19, 0, 21, 24, 27, 29, 1, 31, 33, 35, 2, 37, 38, 3, 40, 4, 41, 6, 43, 45, 7, 47, 48, 8, 50, 9, 51, 11, 52, 12, 54, 13, 55, 15, 16, 56, 18, 20, 57, 22, 59, 23, 60, 25, 26, 61, 28, 30, 32, 62, 34, 36, 39, 42, 63, 44, 46, 49, 53, 58],
      ![6, 11, 15, 18, 20, 21, 0, 25, 28, 30, 31, 1, 34, 36, 37, 2, 39, 40, 3, 41, 4, 5, 44, 46, 47, 7, 49, 50, 8, 51, 9, 10, 53, 54, 12, 55, 13, 14, 56, 16, 17, 19, 58, 59, 22, 60, 23, 24, 61, 26, 27, 29, 62, 32, 33, 35, 38, 63, 42, 43, 45, 48, 52, 57]]) i a
  outside := root 1 * root 3 * root 5 * root 6 * root 7 * root 9
  conj := ![0, 47, 2, 18, 20, 5, 6, 31, 43, 45, 25, 24, 34, 36, 14, 15, 16, 40, 3, 41, 4, 21, 27, 29, 11, 10, 63, 22, 59, 23, 60, 7, 32, 54, 12, 55, 13, 37, 38, 39, 17, 19, 61, 8, 50, 9, 51, 1, 58, 57, 44, 46, 52, 53, 33, 35, 56, 49, 48, 28, 30, 42, 62, 26]
  unconj := ![0, 47, 2, 18, 20, 5, 6, 31, 43, 45, 25, 24, 34, 36, 14, 15, 16, 40, 3, 41, 4, 21, 27, 29, 11, 10, 63, 22, 59, 23, 60, 7, 32, 54, 12, 55, 13, 37, 38, 39, 17, 19, 61, 8, 50, 9, 51, 1, 58, 57, 44, 46, 52, 53, 33, 35, 56, 49, 48, 28, 30, 42, 62, 26]
  squareRoots := ![[], [], [], [1], [1], [], [], [], [], [], [], [], [1], [1], [], [], [], [1], [1], [1],
    [1], [], [], [], [], [], [], [], [], [], [], [], [], [1], [1], [1], [1], [], [], [], [1], [1], [], [],
    [], [], [], [], [], [], [], [], [], [], [1], [1], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid44 : cert44.Valid gen44 := by decide +kernel
private theorem gen_eq44 : Subgroup.closure (Set.range gen44) = smallEvenCandidate 44 := by
  change Subgroup.closure (Set.range gen44) = Subgroup.closure ({root 2 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen44, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate44_hasPCoreNormalizerWitness : (smallEvenCandidate 44).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq44]
  exact cert44.sound (IsPGroup.of_card (n := 12) card) gen44 valid44


end ReeTwo.SylowModel
