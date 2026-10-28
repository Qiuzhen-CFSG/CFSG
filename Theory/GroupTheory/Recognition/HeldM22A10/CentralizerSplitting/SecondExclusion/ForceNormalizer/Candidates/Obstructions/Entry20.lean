module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 20

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

private def cert20 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 7, 1, 60, 11, 6, 12, 59, 61, 10, 39, 13, 58, 32, 38, 33] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3], [0, 1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 11, 12, 13, 8, 9, 10, 15, 14],
    ![2, 5, 0, 8, 9, 1, 11, 12, 3, 4, 14, 6, 7, 15, 10, 13],
    ![3, 7, 8, 0, 10, 12, 13, 1, 2, 14, 4, 15, 5, 6, 9, 11],
    ![4, 6, 9, 10, 0, 11, 1, 13, 14, 2, 3, 5, 15, 7, 8, 12],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 11, 12, 13, 8, 9, 10, 15, 14],
    ![2, 5, 0, 8, 9, 1, 11, 12, 3, 4, 14, 6, 7, 15, 10, 13],
    ![3, 7, 8, 0, 10, 12, 13, 1, 2, 14, 4, 15, 5, 6, 9, 11],
    ![4, 6, 9, 10, 0, 11, 1, 13, 14, 2, 3, 5, 15, 7, 8, 12],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 5, 2, 3, 4, 1, 11, 12, 8, 9, 10, 6, 7, 15, 14, 13]
  unconj := ![0, 5, 2, 3, 4, 1, 11, 12, 8, 9, 10, 6, 7, 15, 14, 13]
  squareRoots := ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

private theorem valid20 : cert20.CenterSquareValid (generator 20) := by
  decide +kernel

/-- Entry 20 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative20_hasPCoreNormalizerWitness :
    (representative 20).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert20.centerSquare_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 20) valid20

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
