module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 13

The displacements descend the characteristic series given by the
involution-generated and square-generated subgroups. The corresponding kernel is a normal two-subgroup
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

private def cert13 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 20, 15, 38, 39, 117, 82, 83, 57, 56, 1, 43, 42, 21, 14, 116] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3], [0, 1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 11, 12, 13, 8, 9, 10, 15, 14],
    ![2, 5, 3, 8, 9, 6, 11, 12, 0, 10, 14, 1, 13, 15, 4, 7],
    ![3, 6, 8, 0, 10, 11, 1, 13, 2, 14, 4, 5, 15, 7, 9, 12],
    ![4, 7, 9, 10, 0, 12, 13, 1, 14, 2, 3, 15, 5, 6, 8, 11],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 11, 12, 13, 8, 9, 10, 15, 14],
    ![8, 11, 0, 2, 14, 1, 5, 15, 3, 4, 9, 6, 7, 12, 10, 13],
    ![3, 6, 8, 0, 10, 11, 1, 13, 2, 14, 4, 5, 15, 7, 9, 12],
    ![4, 7, 9, 10, 0, 12, 13, 1, 14, 2, 3, 15, 5, 6, 8, 11],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 6, 14, 3, 4, 12, 1, 13, 9, 8, 10, 15, 5, 7, 2, 11]
  unconj := ![0, 6, 14, 3, 4, 12, 1, 13, 9, 8, 10, 15, 5, 7, 2, 11]
  squareRoots := ![[], [2], [], [], [], [], [2], [2], [], [], [], [], [], [2], [], []]

private theorem valid13 : cert13.Valid (generator 13) := by
  decide +kernel

/-- Entry 13 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative13_hasPCoreNormalizerWitness :
    (representative 13).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert13.sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 13) valid13

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
