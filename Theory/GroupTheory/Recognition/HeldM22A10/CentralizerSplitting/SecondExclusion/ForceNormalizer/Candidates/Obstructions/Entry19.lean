module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 19

The displacements descend the characteristic series given by the
center and the square-generated subgroup. The corresponding kernel is a normal two-subgroup
of the full intrinsic automorphism group. The witness is `Model.element
24`, represented here by its Sylow index 8.

Positive words and generator/inverse transitions certify the complete subgroup
enumeration. Conjugation, nonmembership and square identities are checked on
the actual permutations by kernel reduction. Source: the intermediate finite
calculation for Huppert--Blackburn III, XII.1.18(b), printed p.314. Reproduce
the proposed tables with `Obstructions/source/generate.py`; no external group
property or automorphism calculation is assumed.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
open Subgroup

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false

private def cert19 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 4, 1, 2, 39, 5, 6, 35, 3, 38, 7, 37, 34, 33, 36, 32] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 3], [0, 1, 3], [0, 2, 3], [1, 2, 3], [2, 0, 3]]
  base := 0
  next := fun j a => (![![1, 2, 5, 6, 7, 0, 8, 9, 10, 12, 3, 13, 4, 14, 15, 11],
    ![2, 5, 0, 8, 9, 1, 10, 12, 3, 4, 6, 14, 7, 15, 11, 13],
    ![3, 10, 8, 0, 11, 6, 5, 15, 2, 14, 1, 4, 13, 12, 9, 7],
    ![4, 7, 9, 11, 0, 12, 13, 1, 14, 2, 15, 3, 5, 6, 8, 10],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![5, 0, 1, 10, 12, 2, 3, 4, 6, 7, 8, 15, 9, 11, 13, 14],
    ![2, 5, 0, 8, 9, 1, 10, 12, 3, 4, 6, 14, 7, 15, 11, 13],
    ![3, 10, 8, 0, 11, 6, 5, 15, 2, 14, 1, 4, 13, 12, 9, 7],
    ![4, 7, 9, 11, 0, 12, 13, 1, 14, 2, 15, 3, 5, 6, 8, 10],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 8
  conj := ![0, 12, 2, 3, 4, 7, 15, 5, 8, 9, 13, 11, 1, 10, 14, 6]
  unconj := ![0, 12, 2, 3, 4, 7, 15, 5, 8, 9, 13, 11, 1, 10, 14, 6]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

private theorem valid19 : cert19.CenterSquareValid (generator 19) := by
  decide +kernel

/-- Entry 19 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative19_hasPCoreNormalizerWitness :
    (representative 19).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert19.centerSquare_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 19) valid19

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
