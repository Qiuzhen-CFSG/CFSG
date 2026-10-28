module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 53

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

-- Candidate 53, diagnostic label 849.
private def gen53 : Fin 5 → SylowModel :=
  ![root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def cert53 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9,
    root 7 * root 8, root 8 * root 9, root 9, rootOne ^ 2 * root 3 * root 4 * root 6 * root 8 * root 9, root 2 * root 5 * root 7 * root 8 * root 9,
    root 2 * root 5 * root 8, root 2 * root 5, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 8 * root 9,
    rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7,
    root 7 * root 9, root 7 * root 8 * root 9, root 8, rootOne ^ 2 * root 3 * root 4 * root 6 * root 7 * root 9,
    rootOne ^ 2 * root 3 * root 4 * root 6, rootOne ^ 2 * root 3 * root 4 * root 6 * root 8, root 2 * root 5 * root 7,
    root 2 * root 5 * root 7 * root 8, root 2 * root 5 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6,
    rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9,
    root 7, rootOne ^ 2 * root 3 * root 4 * root 6 * root 7 * root 8, rootOne ^ 2 * root 3 * root 4 * root 6 * root 7,
    rootOne ^ 2 * root 3 * root 4 * root 6 * root 9, root 2 * root 5 * root 7 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 9,
    rootOne ^ 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 3],
    [2, 4], [3, 4], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [1, 2, 3], [1, 2, 4],
    [1, 3, 4], [2, 3, 4], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4]]
  base := 0
  next := fun i a => (![![1, 5, 6, 7, 8, 9, 12, 14, 15, 0, 16, 17, 18, 19, 20, 21, 23, 24, 2, 25, 3, 4, 26, 27, 28, 29, 30, 10, 11, 13, 31, 22],
      ![2, 6, 0, 10, 11, 12, 1, 16, 17, 18, 3, 4, 5, 22, 23, 24, 7, 8, 9, 26, 27, 28, 13, 14, 15, 30, 19, 20, 21, 31, 25, 29],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  prev := fun i a => (![![9, 0, 18, 20, 21, 1, 2, 3, 4, 5, 27, 28, 6, 29, 7, 8, 10, 11, 12, 13, 14, 15, 31, 16, 17, 19, 22, 23, 24, 25, 26, 30],
      ![2, 6, 0, 10, 11, 12, 1, 16, 17, 18, 3, 4, 5, 22, 23, 24, 7, 8, 9, 26, 27, 28, 13, 14, 15, 30, 19, 20, 21, 31, 25, 29],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  outside := root 2 * root 3 * root 4 * root 7
  conj := ![0, 20, 2, 3, 4, 5, 27, 9, 29, 7, 10, 11, 12, 13, 14, 15, 18, 31, 16, 21, 1, 19, 22, 23, 24, 25, 28, 6, 26, 8, 30, 17]
  unconj := ![0, 20, 2, 3, 4, 5, 27, 9, 29, 7, 10, 11, 12, 13, 14, 15, 18, 31, 16, 21, 1, 19, 22, 23, 24, 25, 28, 6, 26, 8, 30, 17]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid53 : cert53.Valid gen53 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq53 : Subgroup.closure (Set.range gen53) = smallEvenCandidate 53 := by
  change Subgroup.closure (Set.range gen53) = Subgroup.closure ({root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen53, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate53_hasPCoreNormalizerWitness : (smallEvenCandidate 53).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq53]
  exact cert53.sound (IsPGroup.of_card (n := 12) card) gen53 valid53


end ReeTwo.SylowModel
