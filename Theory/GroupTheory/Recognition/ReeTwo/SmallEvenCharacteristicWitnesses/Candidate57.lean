module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 57

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

-- Candidate 57, diagnostic label 871.
private def gen57 : Fin 5 → SylowModel :=
  ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9]
private def cert57 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9,
    root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9, root 1 * root 4 * root 7, root 0 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8,
    root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 0 * root 2 * root 3 * root 4 * root 7 * root 9,
    root 5 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 7 * root 9, root 0 * root 1 * root 2 * root 3 * root 5 * root 6,
    root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 9, root 6 * root 8 * root 9,
    root 0 * root 2 * root 3 * root 4 * root 5 * root 8, root 1 * root 4 * root 6 * root 7 * root 8, root 1 * root 4 * root 5 * root 8 * root 9,
    root 1 * root 4 * root 7 * root 9, root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 9, root 0 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9,
    root 0 * root 1 * root 2 * root 3 * root 5 * root 6 * root 9, root 5 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 5 * root 8,
    root 0 * root 1 * root 2 * root 3 * root 7, root 1 * root 4 * root 5 * root 8, root 0 * root 2 * root 3 * root 4 * root 5 * root 6,
    root 1 * root 4 * root 5 * root 6 * root 9, root 1 * root 4 * root 6 * root 7 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 5 * root 8 * root 9,
    root 1 * root 4 * root 5 * root 6]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 1], [1, 2], [1, 3], [1, 4],
    [2, 3], [2, 4], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [1, 1, 1], [1, 1, 2],
    [1, 2, 3], [1, 2, 4], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 2, 3], [0, 1, 2, 4], [1, 1, 1, 2], [0, 1, 1, 1, 2]]
  base := 0
  next := fun i a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 16, 17, 18, 19, 20, 21, 10, 11, 12, 13, 14, 15, 26, 27, 28, 29, 22, 23, 24, 25, 31, 30],
      ![2, 6, 10, 11, 12, 13, 16, 17, 18, 19, 22, 23, 5, 4, 24, 25, 26, 27, 9, 8, 28, 29, 0, 30, 15, 14, 1, 31, 21, 20, 3, 7],
      ![3, 7, 11, 0, 14, 15, 17, 1, 20, 21, 23, 2, 24, 25, 4, 5, 27, 6, 28, 29, 8, 9, 30, 10, 12, 13, 31, 16, 18, 19, 22, 26],
      ![4, 8, 12, 14, 0, 10, 18, 20, 1, 16, 5, 24, 2, 22, 3, 23, 9, 28, 6, 26, 7, 27, 13, 15, 11, 30, 19, 21, 17, 31, 25, 29],
      ![5, 9, 13, 15, 10, 0, 19, 21, 16, 1, 4, 25, 22, 2, 23, 3, 8, 29, 26, 6, 27, 7, 12, 14, 30, 11, 18, 20, 31, 17, 24, 28]]) i a
  prev := fun i a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 16, 17, 18, 19, 20, 21, 10, 11, 12, 13, 14, 15, 26, 27, 28, 29, 22, 23, 24, 25, 31, 30],
      ![22, 26, 0, 30, 13, 12, 1, 31, 19, 18, 2, 3, 4, 5, 25, 24, 6, 7, 8, 9, 29, 28, 10, 11, 14, 15, 16, 17, 20, 21, 23, 27],
      ![3, 7, 11, 0, 14, 15, 17, 1, 20, 21, 23, 2, 24, 25, 4, 5, 27, 6, 28, 29, 8, 9, 30, 10, 12, 13, 31, 16, 18, 19, 22, 26],
      ![4, 8, 12, 14, 0, 10, 18, 20, 1, 16, 5, 24, 2, 22, 3, 23, 9, 28, 6, 26, 7, 27, 13, 15, 11, 30, 19, 21, 17, 31, 25, 29],
      ![5, 9, 13, 15, 10, 0, 19, 21, 16, 1, 4, 25, 22, 2, 23, 3, 8, 29, 26, 6, 27, 7, 12, 14, 30, 11, 18, 20, 31, 17, 24, 28]]) i a
  outside := root 6 * root 7 * root 8
  conj := ![0, 1, 13, 3, 4, 5, 19, 7, 8, 9, 10, 25, 22, 2, 14, 15, 16, 29, 26, 6, 20, 21, 12, 23, 30, 11, 18, 27, 31, 17, 24, 28]
  unconj := ![0, 1, 13, 3, 4, 5, 19, 7, 8, 9, 10, 25, 22, 2, 14, 15, 16, 29, 26, 6, 20, 21, 12, 23, 30, 11, 18, 27, 31, 17, 24, 28]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid57 : cert57.Valid gen57 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq57 : Subgroup.closure (Set.range gen57) = smallEvenCandidate 57 := by
  change Subgroup.closure (Set.range gen57) = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel)
  congr 1
  simp only [gen57, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate57_hasPCoreNormalizerWitness : (smallEvenCandidate 57).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq57]
  exact cert57.sound (IsPGroup.of_card (n := 12) card) gen57 valid57


end ReeTwo.SylowModel
