module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 16

The displacements descend the characteristic series given by the
center and the square-generated subgroup. The corresponding kernel is a normal two-subgroup
of the full intrinsic automorphism group. The witness is `Model.element
8`, represented here by its Sylow index 2.

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

private def cert16 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 15, 1, 9, 39, 38, 14, 33, 56, 8, 7, 62, 57, 63, 32, 6] a)
  words := ![[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 2], [2, 0], [2, 3], [0, 0, 0], [0, 0, 2], [0, 1, 2], [0, 2, 3]]
  base := 0
  next := fun j a => (![![1, 5, 6, 7, 8, 12, 4, 13, 2, 14, 3, 15, 0, 10, 11, 9],
    ![2, 6, 0, 9, 5, 4, 1, 14, 12, 3, 15, 13, 8, 11, 7, 10],
    ![3, 10, 9, 0, 11, 13, 15, 12, 14, 2, 1, 4, 7, 5, 8, 6],
    ![4, 8, 5, 11, 0, 2, 12, 15, 1, 13, 14, 3, 6, 9, 10, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![12, 0, 8, 10, 6, 1, 2, 3, 4, 15, 13, 14, 5, 7, 9, 11],
    ![2, 6, 0, 9, 5, 4, 1, 14, 12, 3, 15, 13, 8, 11, 7, 10],
    ![3, 10, 9, 0, 11, 13, 15, 12, 14, 2, 1, 4, 7, 5, 8, 6],
    ![4, 8, 5, 11, 0, 2, 12, 15, 1, 13, 14, 3, 6, 9, 10, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 6, 2, 3, 4, 5, 1, 14, 12, 9, 15, 11, 8, 13, 7, 10]
  unconj := ![0, 6, 2, 3, 4, 5, 1, 14, 12, 9, 15, 11, 8, 13, 7, 10]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

private theorem valid16 : cert16.CenterSquareValid (generator 16) := by
  decide +kernel

/-- Entry 16 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative16_hasPCoreNormalizerWitness :
    (representative 16).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert16.centerSquare_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 16) valid16

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
