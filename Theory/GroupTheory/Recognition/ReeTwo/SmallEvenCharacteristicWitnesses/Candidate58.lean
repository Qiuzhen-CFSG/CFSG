module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 58

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

-- Candidate 58, diagnostic label 873.
private def gen58 : Fin 5 → SylowModel :=
  ![root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def cert58 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9,
    root 6 * root 7 * root 9, root 9, root 1 * root 2 * root 3 * root 4 * root 9, root 0 * root 4 * root 5 * root 7,
    root 0 * root 4 * root 6 * root 7 * root 8, root 0 * root 4 * root 8, root 0 * root 1 * root 2 * root 3 * root 5 * root 6 * root 7 * root 9,
    root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8 * root 9,
    root 5 * root 6 * root 8, root 5 * root 7 * root 8, root 6 * root 7, root 1 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8,
    root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 1 * root 2 * root 3 * root 4, root 0 * root 4 * root 5 * root 6 * root 9,
    root 0 * root 4 * root 5 * root 7 * root 9, root 0 * root 4 * root 6 * root 7 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 5,
    root 0 * root 1 * root 2 * root 3 * root 5 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 7 * root 8,
    root 5 * root 6 * root 8 * root 9, root 1 * root 2 * root 3 * root 4 * root 5 * root 6 * root 8 * root 9,
    root 1 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 9,
    root 0 * root 4 * root 5 * root 6, root 0 * root 1 * root 2 * root 3 * root 5 * root 9, root 1 * root 2 * root 3 * root 4 * root 5 * root 6 * root 8]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 3],
    [2, 4], [3, 4], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [1, 2, 3], [1, 2, 4],
    [1, 3, 4], [2, 3, 4], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4], [0, 1, 2, 3, 4]]
  base := 0
  next := fun i a => (![![1, 4, 6, 7, 8, 9, 11, 13, 0, 15, 16, 17, 18, 19, 20, 21, 22, 2, 24, 3, 25, 5, 26, 27, 28, 29, 10, 30, 12, 14, 31, 23],
      ![2, 6, 3, 10, 11, 12, 7, 16, 17, 18, 0, 13, 14, 22, 23, 24, 1, 19, 20, 26, 27, 28, 4, 5, 25, 30, 8, 9, 29, 31, 15, 21],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  prev := fun i a => (![![8, 0, 17, 19, 1, 21, 2, 3, 4, 5, 26, 6, 28, 7, 29, 9, 10, 11, 12, 13, 14, 15, 16, 31, 18, 20, 22, 23, 24, 25, 27, 30],
      ![10, 16, 0, 2, 22, 23, 1, 6, 26, 27, 3, 4, 5, 11, 12, 30, 7, 8, 9, 17, 18, 31, 13, 14, 15, 24, 19, 20, 21, 28, 25, 29],
      ![3, 7, 10, 0, 13, 14, 16, 1, 19, 20, 2, 22, 23, 4, 5, 25, 6, 26, 27, 8, 9, 29, 11, 12, 30, 15, 17, 18, 31, 21, 24, 28],
      ![4, 8, 11, 13, 0, 15, 17, 19, 1, 21, 22, 2, 24, 3, 25, 5, 26, 6, 28, 7, 29, 9, 10, 30, 12, 14, 16, 31, 18, 20, 23, 27],
      ![5, 9, 12, 14, 15, 0, 18, 20, 21, 1, 23, 24, 2, 25, 3, 4, 27, 28, 6, 29, 7, 8, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26]]) i a
  outside := root 6
  conj := ![0, 1, 12, 3, 4, 5, 18, 7, 8, 9, 23, 24, 2, 13, 14, 15, 27, 28, 6, 19, 20, 21, 30, 10, 11, 25, 31, 16, 17, 29, 22, 26]
  unconj := ![0, 1, 12, 3, 4, 5, 18, 7, 8, 9, 23, 24, 2, 13, 14, 15, 27, 28, 6, 19, 20, 21, 30, 10, 11, 25, 31, 16, 17, 29, 22, 26]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid58 : cert58.Valid gen58 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq58 : Subgroup.closure (Set.range gen58) = smallEvenCandidate 58 := by
  change Subgroup.closure (Set.range gen58) = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen58, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate58_hasPCoreNormalizerWitness : (smallEvenCandidate 58).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq58]
  exact cert58.sound (IsPGroup.of_card (n := 12) card) gen58 valid58


end ReeTwo.SylowModel
