module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 34

Every displacement is a product of squares, so the action is trivial
on the Frattini quotient. The corresponding kernel is a normal two-subgroup
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

private def cert34 : InvolutionSquareCertificate Model.sylowSubgroup 7 32 where
  rep := fun a => Model.sylowElement (![0, 20, 4, 1, 2, 39, 17, 21, 22, 83, 16, 5, 6, 35, 3, 38, 80, 7, 37, 19, 86, 23, 82, 36, 18, 81, 87, 34, 84, 33, 85, 32] a)
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 0], [3, 1], [3, 4], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 0], [0, 3, 1], [0, 3, 4], [1, 0, 4], [1, 2, 4], [1, 3, 0], [1, 3, 4], [3, 1, 0], [3, 1, 4]]
  base := 0
  next := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 11, 10, 19, 20, 21, 22, 23, 24, 25, 12, 13, 14, 15, 16, 17, 18, 27, 26, 29, 28, 31, 30],
    ![2, 10, 3, 11, 12, 13, 1, 6, 24, 26, 7, 0, 14, 15, 17, 27, 28, 4, 29, 8, 9, 19, 20, 31, 21, 30, 22, 5, 25, 23, 16, 18],
    ![3, 7, 11, 0, 14, 15, 10, 1, 21, 22, 6, 2, 17, 27, 4, 5, 25, 12, 23, 24, 26, 8, 9, 18, 19, 16, 20, 13, 30, 31, 28, 29],
    ![4, 16, 17, 14, 0, 18, 28, 25, 22, 21, 30, 12, 11, 31, 3, 23, 1, 2, 5, 20, 19, 9, 8, 15, 26, 7, 24, 29, 6, 27, 10, 13],
    ![5, 9, 13, 15, 18, 0, 20, 22, 25, 1, 26, 27, 29, 2, 23, 3, 21, 31, 4, 28, 6, 16, 7, 14, 30, 8, 10, 11, 19, 12, 24, 17],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  prev := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 11, 10, 19, 20, 21, 22, 23, 24, 25, 12, 13, 14, 15, 16, 17, 18, 27, 26, 29, 28, 31, 30],
    ![11, 6, 0, 2, 17, 27, 7, 10, 19, 20, 1, 3, 4, 5, 12, 13, 30, 14, 31, 21, 22, 24, 26, 29, 8, 28, 9, 15, 16, 18, 25, 23],
    ![3, 7, 11, 0, 14, 15, 10, 1, 21, 22, 6, 2, 17, 27, 4, 5, 25, 12, 23, 24, 26, 8, 9, 18, 19, 16, 20, 13, 30, 31, 28, 29],
    ![4, 16, 17, 14, 0, 18, 28, 25, 22, 21, 30, 12, 11, 31, 3, 23, 1, 2, 5, 20, 19, 9, 8, 15, 26, 7, 24, 29, 6, 27, 10, 13],
    ![5, 9, 13, 15, 18, 0, 20, 22, 25, 1, 26, 27, 29, 2, 23, 3, 21, 31, 4, 28, 6, 16, 7, 14, 30, 8, 10, 11, 19, 12, 24, 17],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  outside := Model.sylowElement 8
  conj := ![0, 9, 27, 3, 4, 5, 10, 22, 25, 1, 6, 13, 31, 11, 14, 15, 21, 29, 18, 24, 26, 16, 7, 23, 19, 8, 20, 2, 30, 17, 28, 12]
  unconj := ![0, 9, 27, 3, 4, 5, 10, 22, 25, 1, 6, 13, 31, 11, 14, 15, 21, 29, 18, 24, 26, 16, 7, 23, 19, 8, 20, 2, 30, 17, 28, 12]
  squareRoots := ![[], [19], [8], [], [], [], [2], [19], [19], [19], [2], [8], [8], [8], [], [], [19], [8], [], [2], [2], [19], [19], [], [2], [19], [2], [8], [2], [8], [2], [8]]

private theorem valid34 : cert34.FrattiniValid (generator 34) := by
  decide +kernel

/-- Entry 34 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative34_hasPCoreNormalizerWitness :
    (representative 34).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert34.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 34) valid34

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
