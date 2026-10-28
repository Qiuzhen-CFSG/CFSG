module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 23

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

private def cert23 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 20, 4, 1, 39, 17, 21, 83, 16, 5, 35, 38, 86, 82, 87, 34] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 3], [0, 1, 3], [0, 2, 3], [1, 0, 3], [1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 9, 8, 12, 13, 10, 11, 15, 14],
    ![2, 8, 3, 9, 10, 1, 5, 14, 6, 0, 11, 15, 7, 12, 13, 4],
    ![3, 6, 9, 0, 11, 8, 1, 13, 5, 2, 15, 4, 14, 7, 12, 10],
    ![4, 7, 10, 11, 0, 12, 13, 1, 14, 15, 2, 3, 5, 6, 8, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 9, 8, 12, 13, 10, 11, 15, 14],
    ![9, 5, 0, 2, 15, 6, 8, 12, 1, 3, 4, 10, 13, 14, 7, 11],
    ![3, 6, 9, 0, 11, 8, 1, 13, 5, 2, 15, 4, 14, 7, 12, 10],
    ![4, 7, 10, 11, 0, 12, 13, 1, 14, 15, 2, 3, 5, 6, 8, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 13, 9, 3, 4, 12, 7, 6, 14, 2, 15, 11, 5, 1, 8, 10]
  unconj := ![0, 13, 9, 3, 4, 12, 7, 6, 14, 2, 15, 11, 5, 1, 8, 10]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

private theorem valid23 : cert23.CenterSquareValid (generator 23) := by
  decide +kernel

/-- Entry 23 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative23_hasPCoreNormalizerWitness :
    (representative 23).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert23.centerSquare_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 23) valid23

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
