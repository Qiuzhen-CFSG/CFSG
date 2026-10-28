module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 52

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

-- Candidate 52, diagnostic label 831.
private def gen52 : Fin 5 → SylowModel :=
  ![root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9]
private def cert52 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9,
    root 7 * root 9, root 9, root 5 * root 6 * root 8 * root 9, root 0 * root 3 * root 5 * root 8 * root 9,
    root 0 * root 3 * root 8 * root 9, root 0 * root 3 * root 5 * root 6 * root 9, root 0 * root 3 * root 5 * root 6 * root 7 * root 9,
    root 5, root 6 * root 8, root 6 * root 7 * root 8, root 5 * root 6 * root 8, root 5 * root 6 * root 7 * root 8,
    root 7, root 0 * root 3 * root 7 * root 8 * root 9, root 5 * root 7, root 0 * root 3 * root 6 * root 7,
    root 0 * root 3 * root 5 * root 7 * root 8, root 0 * root 3 * root 5 * root 8, root 0 * root 3 * root 7 * root 8,
    root 0 * root 3 * root 8, root 0 * root 3 * root 5 * root 6, root 5 * root 7 * root 9, root 5 * root 9,
    root 6 * root 8 * root 9, root 0 * root 3 * root 6, root 0 * root 3 * root 6 * root 9, root 0 * root 3 * root 6 * root 7 * root 9,
    root 0 * root 3 * root 5 * root 7 * root 8 * root 9]
  words := ![[], [0], [1], [2], [3], [4], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4],
    [2, 3], [2, 4], [3, 4], [0, 0, 0], [0, 0, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4],
    [1, 2, 3], [1, 2, 4], [1, 3, 4], [0, 0, 0, 1], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4]]
  base := 0
  next := fun i a => (![![1, 6, 7, 8, 9, 10, 17, 18, 16, 15, 14, 19, 20, 21, 22, 23, 24, 0, 28, 27, 26, 25, 5, 4, 3, 29, 30, 31, 2, 13, 12, 11],
      ![2, 7, 0, 11, 12, 13, 18, 1, 19, 20, 21, 3, 4, 5, 25, 26, 27, 28, 6, 8, 9, 10, 29, 30, 31, 14, 15, 16, 17, 22, 23, 24],
      ![3, 8, 11, 0, 14, 15, 16, 19, 1, 22, 23, 2, 25, 26, 4, 5, 6, 24, 27, 7, 29, 30, 9, 10, 17, 12, 13, 18, 31, 20, 21, 28],
      ![4, 9, 12, 14, 0, 16, 15, 20, 22, 1, 24, 25, 2, 27, 3, 6, 5, 23, 26, 29, 7, 31, 8, 17, 10, 11, 18, 13, 30, 19, 28, 21],
      ![5, 10, 13, 15, 16, 0, 14, 21, 23, 24, 1, 26, 27, 2, 6, 3, 4, 22, 25, 30, 31, 7, 17, 8, 9, 18, 11, 12, 29, 28, 19, 20]]) i a
  prev := fun i a => (![![17, 0, 28, 24, 23, 22, 1, 2, 3, 4, 5, 31, 30, 29, 10, 9, 8, 6, 7, 11, 12, 13, 14, 15, 16, 21, 20, 19, 18, 25, 26, 27],
      ![2, 7, 0, 11, 12, 13, 18, 1, 19, 20, 21, 3, 4, 5, 25, 26, 27, 28, 6, 8, 9, 10, 29, 30, 31, 14, 15, 16, 17, 22, 23, 24],
      ![3, 8, 11, 0, 14, 15, 16, 19, 1, 22, 23, 2, 25, 26, 4, 5, 6, 24, 27, 7, 29, 30, 9, 10, 17, 12, 13, 18, 31, 20, 21, 28],
      ![4, 9, 12, 14, 0, 16, 15, 20, 22, 1, 24, 25, 2, 27, 3, 6, 5, 23, 26, 29, 7, 31, 8, 17, 10, 11, 18, 13, 30, 19, 28, 21],
      ![5, 10, 13, 15, 16, 0, 14, 21, 23, 24, 1, 26, 27, 2, 6, 3, 4, 22, 25, 30, 31, 7, 17, 8, 9, 18, 11, 12, 29, 28, 19, 20]]) i a
  outside := root 6
  conj := ![0, 10, 2, 3, 4, 5, 6, 21, 23, 24, 1, 11, 12, 13, 14, 15, 16, 22, 18, 30, 31, 7, 17, 8, 9, 25, 26, 27, 29, 28, 19, 20]
  unconj := ![0, 10, 2, 3, 4, 5, 6, 21, 23, 24, 1, 11, 12, 13, 14, 15, 16, 22, 18, 30, 31, 7, 17, 8, 9, 25, 26, 27, 29, 28, 19, 20]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid52 : cert52.Valid gen52 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq52 : Subgroup.closure (Set.range gen52) = smallEvenCandidate 52 := by
  change Subgroup.closure (Set.range gen52) = Subgroup.closure ({root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen52, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate52_hasPCoreNormalizerWitness : (smallEvenCandidate 52).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq52]
  exact cert52.sound (IsPGroup.of_card (n := 12) card) gen52 valid52


end ReeTwo.SylowModel
