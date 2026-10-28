module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 33

Every displacement is a product of squares, so the action is trivial
on the Frattini quotient. The corresponding kernel is a normal two-subgroup
of the full intrinsic automorphism group. The witness is `Model.element
12`, represented here by its Sylow index 4.

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

private def cert33 : InvolutionSquareCertificate Model.sylowSubgroup 7 32 where
  rep := fun a => Model.sylowElement (![0, 20, 15, 1, 2, 39, 117, 21, 22, 83, 38, 14, 13, 56, 3, 80, 12, 37, 82, 116, 119, 42, 23, 36, 118, 81, 57, 41, 58, 40, 59, 43] a)
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 1], [1, 2], [1, 3], [1, 4], [2, 3], [3, 0], [3, 1], [3, 4], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 3, 0], [0, 3, 1], [0, 3, 4], [1, 1, 1], [1, 3, 0], [1, 3, 4], [3, 0, 1], [3, 1, 4], [0, 1, 1, 1]]
  base := 0
  next := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 18, 19, 20, 21, 22, 23, 24, 25, 10, 11, 12, 13, 14, 15, 16, 17, 31, 30, 29, 28, 27, 26],
    ![2, 6, 10, 11, 12, 13, 18, 19, 20, 21, 26, 5, 23, 3, 16, 27, 17, 28, 31, 9, 15, 7, 24, 30, 25, 29, 0, 8, 14, 22, 4, 1],
    ![3, 7, 11, 0, 14, 10, 19, 1, 22, 18, 5, 2, 16, 26, 4, 25, 12, 23, 9, 6, 24, 31, 8, 17, 20, 15, 13, 29, 30, 27, 28, 21],
    ![4, 15, 16, 14, 0, 17, 29, 25, 18, 22, 23, 12, 11, 30, 3, 1, 2, 5, 8, 27, 21, 20, 9, 10, 31, 7, 28, 19, 26, 6, 13, 24],
    ![5, 9, 13, 10, 17, 0, 21, 18, 25, 1, 3, 26, 28, 2, 23, 22, 30, 4, 7, 31, 29, 6, 15, 14, 27, 8, 11, 24, 12, 20, 16, 19],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  prev := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 18, 19, 20, 21, 22, 23, 24, 25, 10, 11, 12, 13, 14, 15, 16, 17, 31, 30, 29, 28, 27, 26],
    ![26, 31, 0, 13, 30, 11, 1, 21, 27, 19, 2, 3, 4, 5, 28, 20, 14, 16, 6, 7, 8, 9, 29, 12, 22, 24, 10, 15, 17, 25, 23, 18],
    ![3, 7, 11, 0, 14, 10, 19, 1, 22, 18, 5, 2, 16, 26, 4, 25, 12, 23, 9, 6, 24, 31, 8, 17, 20, 15, 13, 29, 30, 27, 28, 21],
    ![4, 15, 16, 14, 0, 17, 29, 25, 18, 22, 23, 12, 11, 30, 3, 1, 2, 5, 8, 27, 21, 20, 9, 10, 31, 7, 28, 19, 26, 6, 13, 24],
    ![5, 9, 13, 10, 17, 0, 21, 18, 25, 1, 3, 26, 28, 2, 23, 22, 30, 4, 7, 31, 29, 6, 15, 14, 27, 8, 11, 24, 12, 20, 16, 19],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  outside := Model.sylowElement 4
  conj := ![0, 7, 13, 3, 14, 5, 31, 1, 8, 18, 10, 26, 30, 2, 4, 15, 28, 23, 9, 21, 29, 19, 22, 17, 27, 25, 11, 24, 16, 20, 12, 6]
  unconj := ![0, 7, 13, 3, 14, 5, 31, 1, 8, 18, 10, 26, 30, 2, 4, 15, 28, 23, 9, 21, 29, 19, 22, 17, 27, 25, 11, 24, 16, 20, 12, 6]
  squareRoots := ![[], [20], [12], [], [20], [], [2], [20], [], [20], [], [12], [2], [12], [20], [], [2], [20], [20], [2], [12], [2], [], [20], [12], [], [12], [12], [2], [12], [2], [2]]

private theorem valid33 : cert33.FrattiniValid (generator 33) := by
  decide +kernel

/-- Entry 33 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative33_hasPCoreNormalizerWitness :
    (representative 33).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert33.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 33) valid33

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
