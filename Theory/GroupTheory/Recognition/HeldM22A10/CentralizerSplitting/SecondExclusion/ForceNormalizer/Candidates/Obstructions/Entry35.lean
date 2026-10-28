module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 35

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

private def cert35 : InvolutionSquareCertificate Model.sylowSubgroup 7 32 where
  rep := fun a => Model.sylowElement (![0, 80, 7, 1, 60, 11, 38, 87, 81, 115, 44, 17, 6, 12, 59, 61, 10, 114, 39, 45, 22, 33, 86, 43, 116, 23, 16, 117, 42, 13, 58, 32] a)
  words := ![[], [0], [1], [2], [3], [4], [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 0], [3, 4], [4, 0], [0, 0, 0], [0, 0, 1], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 3, 4], [1, 0, 2], [1, 0, 3], [1, 0, 4], [1, 2, 3], [1, 2, 4], [1, 3, 4]]
  base := 0
  next := fun j a => (![![1, 6, 7, 8, 9, 10, 20, 21, 18, 16, 15, 2, 22, 23, 24, 17, 19, 5, 25, 4, 0, 11, 31, 30, 29, 3, 12, 13, 14, 28, 27, 26],
    ![2, 11, 0, 12, 13, 14, 21, 20, 26, 27, 28, 1, 3, 4, 5, 29, 30, 24, 31, 23, 7, 6, 25, 19, 17, 22, 8, 9, 10, 15, 16, 18],
    ![3, 8, 12, 0, 15, 16, 18, 22, 1, 17, 19, 26, 2, 29, 30, 4, 5, 9, 6, 10, 25, 31, 7, 28, 27, 20, 11, 24, 23, 13, 14, 21],
    ![4, 17, 14, 15, 0, 18, 16, 27, 9, 8, 20, 23, 30, 31, 2, 3, 6, 1, 5, 25, 10, 29, 24, 11, 22, 19, 28, 7, 26, 21, 12, 13],
    ![5, 19, 13, 16, 18, 0, 15, 28, 10, 20, 8, 24, 29, 2, 31, 6, 3, 25, 4, 1, 9, 30, 23, 22, 11, 17, 27, 26, 7, 12, 21, 14],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  prev := fun j a => (![![20, 0, 11, 25, 19, 17, 1, 2, 3, 4, 5, 21, 26, 27, 28, 10, 9, 15, 8, 16, 6, 7, 12, 13, 14, 18, 31, 30, 29, 24, 23, 22],
    ![2, 11, 0, 12, 13, 14, 21, 20, 26, 27, 28, 1, 3, 4, 5, 29, 30, 24, 31, 23, 7, 6, 25, 19, 17, 22, 8, 9, 10, 15, 16, 18],
    ![3, 8, 12, 0, 15, 16, 18, 22, 1, 17, 19, 26, 2, 29, 30, 4, 5, 9, 6, 10, 25, 31, 7, 28, 27, 20, 11, 24, 23, 13, 14, 21],
    ![4, 17, 14, 15, 0, 18, 16, 27, 9, 8, 20, 23, 30, 31, 2, 3, 6, 1, 5, 25, 10, 29, 24, 11, 22, 19, 28, 7, 26, 21, 12, 13],
    ![5, 19, 13, 16, 18, 0, 15, 28, 10, 20, 8, 24, 29, 2, 31, 6, 3, 25, 4, 1, 9, 30, 23, 22, 11, 17, 27, 26, 7, 12, 21, 14],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 20, 12, 3, 4, 5, 6, 26, 25, 19, 17, 22, 2, 29, 30, 15, 16, 10, 18, 9, 1, 31, 11, 24, 23, 8, 7, 28, 27, 13, 14, 21]
  unconj := ![0, 20, 12, 3, 4, 5, 6, 26, 25, 19, 17, 22, 2, 29, 30, 15, 16, 10, 18, 9, 1, 31, 11, 24, 23, 8, 7, 28, 27, 13, 14, 21]
  squareRoots := ![[], [1], [1, 9], [], [], [], [], [9], [1], [1], [1], [9], [1, 9], [1, 9], [1, 9], [], [], [1], [], [1], [1], [1, 9], [9], [9], [9], [1], [9], [9], [9], [1, 9], [1, 9], [1, 9]]

private theorem valid35 : cert35.FrattiniValid (generator 35) := by
  decide +kernel

/-- Entry 35 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative35_hasPCoreNormalizerWitness :
    (representative 35).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert35.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 35) valid35

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
