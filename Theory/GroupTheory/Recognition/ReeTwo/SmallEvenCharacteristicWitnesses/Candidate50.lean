module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 50

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

-- Candidate 50, diagnostic label 816.
private def gen50 : Fin 5 → SylowModel :=
  ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9]
private def cert50 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8,
    root 7 * root 9, root 9, rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 3 * root 5 * root 9,
    rootOne ^ 2 * root 2 * root 4 * root 5, rootOne ^ 2 * root 2 * root 4 * root 5 * root 7, root 2 * root 3 * root 4 * root 7 * root 9,
    root 7 * root 8, root 8, rootOne ^ 2 * root 3 * root 5 * root 7, root 2 * root 3 * root 4 * root 8 * root 9,
    root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 7, rootOne ^ 2 * root 3 * root 5 * root 8, rootOne ^ 2 * root 2 * root 4 * root 5 * root 8 * root 9,
    rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 3 * root 5, rootOne ^ 2 * root 2 * root 4 * root 5 * root 9,
    rootOne ^ 2 * root 3 * root 5 * root 7 * root 8 * root 9, root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 7,
    root 7 * root 8 * root 9, rootOne ^ 2 * root 3 * root 5 * root 7 * root 9, root 2 * root 3 * root 4 * root 8,
    rootOne ^ 2 * root 3 * root 5 * root 8 * root 9, rootOne ^ 2 * root 2 * root 4 * root 5 * root 8, rootOne ^ 2 * root 3 * root 5 * root 7 * root 8,
    root 2 * root 3 * root 4 * root 9]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 0],
    [2, 3], [2, 4], [3, 4], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 4], [0, 3, 4], [1, 2, 0], [1, 2, 3], [1, 2, 4],
    [1, 3, 4], [2, 0, 4], [2, 3, 4], [0, 1, 2, 4], [0, 1, 3, 4], [1, 2, 0, 4], [1, 2, 3, 4]]
  base := 0
  next := fun i a => (![![1, 4, 6, 7, 8, 9, 11, 14, 0, 16, 17, 18, 19, 3, 13, 20, 21, 23, 2, 25, 27, 5, 10, 22, 28, 29, 15, 26, 31, 12, 24, 30],
      ![2, 6, 0, 10, 11, 12, 1, 17, 18, 19, 3, 4, 5, 22, 23, 24, 25, 7, 8, 9, 28, 29, 13, 14, 15, 16, 30, 31, 20, 21, 26, 27],
      ![3, 13, 10, 4, 14, 15, 22, 1, 7, 26, 11, 23, 24, 8, 0, 16, 27, 6, 17, 30, 9, 20, 18, 2, 25, 31, 21, 5, 19, 28, 29, 12],
      ![4, 8, 11, 14, 0, 16, 18, 13, 1, 21, 23, 2, 25, 7, 3, 27, 5, 22, 6, 29, 26, 9, 17, 10, 31, 12, 20, 15, 30, 19, 28, 24],
      ![5, 9, 12, 15, 16, 0, 19, 20, 21, 1, 24, 25, 2, 26, 27, 3, 4, 28, 29, 6, 7, 8, 30, 31, 10, 11, 13, 14, 17, 18, 22, 23]]) i a
  prev := fun i a => (![![8, 0, 18, 13, 1, 21, 2, 3, 4, 5, 22, 6, 29, 14, 7, 26, 9, 10, 11, 12, 15, 16, 23, 17, 30, 19, 27, 20, 24, 25, 31, 28],
      ![2, 6, 0, 10, 11, 12, 1, 17, 18, 19, 3, 4, 5, 22, 23, 24, 25, 7, 8, 9, 28, 29, 13, 14, 15, 16, 30, 31, 20, 21, 26, 27],
      ![14, 7, 23, 0, 3, 27, 17, 8, 13, 20, 2, 10, 31, 1, 4, 5, 15, 18, 22, 28, 21, 26, 6, 11, 12, 24, 9, 16, 29, 30, 19, 25],
      ![4, 8, 11, 14, 0, 16, 18, 13, 1, 21, 23, 2, 25, 7, 3, 27, 5, 22, 6, 29, 26, 9, 17, 10, 31, 12, 20, 15, 30, 19, 28, 24],
      ![5, 9, 12, 15, 16, 0, 19, 20, 21, 1, 24, 25, 2, 26, 27, 3, 4, 28, 29, 6, 7, 8, 30, 31, 10, 11, 13, 14, 17, 18, 22, 23]]) i a
  outside := rootOne ^ 2
  conj := ![0, 29, 2, 3, 4, 5, 21, 30, 19, 18, 10, 11, 12, 28, 14, 15, 16, 26, 9, 8, 22, 6, 20, 23, 24, 25, 17, 27, 13, 1, 7, 31]
  unconj := ![0, 29, 2, 3, 4, 5, 21, 30, 19, 18, 10, 11, 12, 28, 14, 15, 16, 26, 9, 8, 22, 6, 20, 23, 24, 25, 17, 27, 13, 1, 7, 31]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid50 : cert50.Valid gen50 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq50 : Subgroup.closure (Set.range gen50) = smallEvenCandidate 50 := by
  change Subgroup.closure (Set.range gen50) = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen50, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate50_hasPCoreNormalizerWitness : (smallEvenCandidate 50).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq50]
  exact cert50.sound (IsPGroup.of_card (n := 12) card) gen50 valid50


end ReeTwo.SylowModel
