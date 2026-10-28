module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 36

Every displacement is a product of squares, so the action is trivial
on the Frattini quotient. The corresponding kernel is a normal two-subgroup
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

private def cert36 : InvolutionSquareCertificate Model.sylowSubgroup 7 32 where
  rep := fun a => Model.sylowElement (![0, 80, 4, 1, 60, 11, 38, 84, 81, 115, 44, 5, 15, 56, 61, 10, 114, 39, 45, 22, 34, 85, 40, 119, 23, 14, 57, 41, 35, 118, 18, 19] a)
  words := ![[], [0], [1], [2], [3], [4], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 0], [3, 4], [4, 0], [0, 0, 0], [0, 0, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 3, 4], [1, 2, 3], [1, 2, 4], [1, 3, 0], [1, 3, 4], [1, 4, 0], [0, 0, 0, 1], [0, 1, 3, 4]]
  base := 0
  next := fun j a => (![![1, 6, 7, 8, 9, 10, 19, 20, 17, 15, 14, 21, 22, 23, 16, 18, 5, 24, 4, 0, 30, 28, 26, 25, 3, 27, 29, 13, 31, 12, 2, 11],
    ![2, 7, 3, 11, 12, 13, 20, 8, 21, 22, 23, 0, 14, 15, 25, 26, 27, 28, 29, 30, 17, 1, 16, 18, 31, 4, 5, 9, 6, 10, 24, 19],
    ![3, 8, 11, 0, 14, 15, 17, 21, 1, 16, 18, 2, 25, 26, 4, 5, 9, 6, 10, 24, 28, 7, 27, 29, 19, 12, 13, 22, 20, 23, 31, 30],
    ![4, 16, 13, 14, 0, 17, 15, 29, 9, 8, 19, 26, 28, 2, 3, 6, 1, 5, 24, 10, 25, 23, 30, 21, 18, 20, 11, 31, 12, 7, 22, 27],
    ![5, 18, 12, 15, 17, 0, 14, 27, 10, 19, 8, 25, 2, 28, 6, 3, 24, 4, 1, 9, 26, 22, 21, 30, 16, 11, 20, 7, 13, 31, 23, 29],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  prev := fun j a => (![![19, 0, 30, 24, 18, 16, 1, 2, 3, 4, 5, 31, 29, 27, 10, 9, 14, 8, 15, 6, 7, 11, 12, 13, 17, 23, 22, 25, 21, 26, 20, 28],
    ![11, 21, 0, 2, 25, 26, 28, 1, 7, 27, 29, 3, 4, 5, 12, 13, 22, 20, 23, 31, 6, 8, 9, 10, 30, 14, 15, 16, 17, 18, 19, 24],
    ![3, 8, 11, 0, 14, 15, 17, 21, 1, 16, 18, 2, 25, 26, 4, 5, 9, 6, 10, 24, 28, 7, 27, 29, 19, 12, 13, 22, 20, 23, 31, 30],
    ![4, 16, 13, 14, 0, 17, 15, 29, 9, 8, 19, 26, 28, 2, 3, 6, 1, 5, 24, 10, 25, 23, 30, 21, 18, 20, 11, 31, 12, 7, 22, 27],
    ![5, 18, 12, 15, 17, 0, 14, 27, 10, 19, 8, 25, 2, 28, 6, 3, 24, 4, 1, 9, 26, 22, 21, 30, 16, 11, 20, 7, 13, 31, 23, 29],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 19, 11, 3, 4, 5, 6, 31, 24, 18, 16, 2, 25, 26, 14, 15, 10, 17, 9, 1, 28, 30, 23, 22, 8, 12, 13, 29, 20, 27, 21, 7]
  unconj := ![0, 19, 11, 3, 4, 5, 6, 31, 24, 18, 16, 2, 25, 26, 14, 15, 10, 17, 9, 1, 28, 30, 23, 22, 8, 12, 13, 29, 20, 27, 21, 7]
  squareRoots := ![[], [1], [2], [], [], [], [], [7], [1], [1], [1], [2], [2], [2], [], [], [1], [], [1], [1], [2], [7], [7], [7], [1], [2], [2], [7], [2], [7], [7], [7]]

private theorem valid36 : cert36.FrattiniValid (generator 36) := by
  decide +kernel

/-- Entry 36 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative36_hasPCoreNormalizerWitness :
    (representative 36).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert36.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 36) valid36

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
