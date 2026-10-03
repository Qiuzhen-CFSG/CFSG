module

public import Theory.GroupTheory.NormalizerInvolutionSquareWitness
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates

/-!
# Characteristic-series witness for small even candidate 55

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

-- Candidate 55, diagnostic label 856.
private def gen55 : Fin 5 → SylowModel :=
  ![root 3, root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 5 * root 8, root 8, root 9]
private def cert55 : InvolutionSquareCertificate SylowModel 5 32 where
  rep := ![1, root 3, root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 5 * root 8, root 8, root 9,
    root 1 * root 5 * root 7 * root 9, root 3 * root 5 * root 8, root 3 * root 8, root 3 * root 9, root 5 * root 8 * root 9,
    root 1 * root 3 * root 7 * root 9, root 1 * root 3 * root 5 * root 7 * root 9, root 1 * root 3 * root 5 * root 7 * root 8,
    root 5, root 8 * root 9, root 3 * root 5 * root 8 * root 9, root 1 * root 7 * root 8 * root 9, root 1 * root 5 * root 7 * root 8 * root 9,
    root 1 * root 5 * root 7, root 3 * root 5, root 3 * root 8 * root 9, root 1 * root 3 * root 7, root 5 * root 9,
    root 1 * root 3 * root 7 * root 8 * root 9, root 1 * root 3 * root 5 * root 7, root 1 * root 7 * root 8,
    root 3 * root 5 * root 9, root 1 * root 7 * root 9, root 1 * root 5 * root 7 * root 8, root 1 * root 3 * root 7 * root 8,
    root 1 * root 7]
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 1], [1, 2], [1, 3], [1, 4],
    [2, 3], [3, 4], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 3, 4], [1, 1, 1], [1, 1, 3],
    [1, 2, 3], [1, 3, 4], [0, 1, 1, 1], [0, 1, 1, 3], [0, 1, 2, 3], [0, 1, 3, 4], [1, 1, 1, 3], [0, 1, 1, 1, 3]]
  base := 0
  next := fun i a => (![![1, 4, 6, 7, 8, 9, 12, 14, 0, 15, 16, 17, 18, 19, 20, 21, 23, 24, 2, 25, 3, 5, 26, 27, 28, 29, 30, 10, 11, 13, 31, 22],
      ![2, 6, 10, 11, 12, 13, 16, 17, 18, 19, 22, 5, 23, 3, 24, 25, 26, 9, 27, 7, 28, 29, 0, 30, 15, 14, 1, 31, 21, 20, 4, 8],
      ![3, 7, 11, 0, 14, 10, 17, 1, 20, 16, 5, 2, 24, 22, 4, 23, 9, 6, 28, 26, 8, 27, 13, 15, 12, 30, 19, 21, 18, 31, 25, 29],
      ![4, 8, 12, 14, 0, 15, 18, 20, 1, 21, 23, 24, 2, 25, 3, 5, 27, 28, 6, 29, 7, 9, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26],
      ![5, 9, 13, 10, 15, 0, 19, 16, 21, 1, 3, 22, 25, 2, 23, 4, 7, 26, 29, 6, 27, 8, 11, 14, 30, 12, 17, 20, 31, 18, 24, 28]]) i a
  prev := fun i a => (![![8, 0, 18, 20, 1, 21, 2, 3, 4, 5, 27, 28, 6, 29, 7, 9, 10, 11, 12, 13, 14, 15, 31, 16, 17, 19, 22, 23, 24, 25, 26, 30],
      ![22, 26, 0, 13, 30, 11, 1, 19, 31, 17, 2, 3, 4, 5, 25, 24, 6, 7, 8, 9, 29, 28, 10, 12, 14, 15, 16, 18, 20, 21, 23, 27],
      ![3, 7, 11, 0, 14, 10, 17, 1, 20, 16, 5, 2, 24, 22, 4, 23, 9, 6, 28, 26, 8, 27, 13, 15, 12, 30, 19, 21, 18, 31, 25, 29],
      ![4, 8, 12, 14, 0, 15, 18, 20, 1, 21, 23, 24, 2, 25, 3, 5, 27, 28, 6, 29, 7, 9, 30, 10, 11, 13, 31, 16, 17, 19, 22, 26],
      ![5, 9, 13, 10, 15, 0, 19, 16, 21, 1, 3, 22, 25, 2, 23, 4, 7, 26, 29, 6, 27, 8, 11, 14, 30, 12, 17, 20, 31, 18, 24, 28]]) i a
  outside := root 1 * root 3 * root 5 * root 6 * root 7 * root 9
  conj := ![0, 9, 13, 3, 4, 5, 6, 16, 21, 1, 10, 22, 25, 2, 14, 15, 7, 17, 18, 19, 27, 8, 11, 23, 30, 12, 26, 20, 28, 29, 24, 31]
  unconj := ![0, 9, 13, 3, 4, 5, 6, 16, 21, 1, 10, 22, 25, 2, 14, 15, 7, 17, 18, 19, 27, 8, 11, 23, 30, 12, 26, 20, 28, 29, 24, 31]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], []]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem valid55 : cert55.Valid gen55 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem gen_eq55 : Subgroup.closure (Set.range gen55) = smallEvenCandidate 55 := by
  change Subgroup.closure (Set.range gen55) = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 5 * root 8, root 8, root 9} : Set SylowModel)
  congr 1
  simp only [gen55, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
/-- The certified characteristic-series witness for this fixed representative. -/
public theorem smallEvenCandidate55_hasPCoreNormalizerWitness : (smallEvenCandidate 55).HasPCoreNormalizerWitness 2 := by
  rw [← gen_eq55]
  exact cert55.sound (IsPGroup.of_card (n := 12) card) gen55 valid55


end ReeTwo.SylowModel
