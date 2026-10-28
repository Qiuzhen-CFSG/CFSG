module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 27

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

private def cert27 : InvolutionSquareCertificate Model.sylowSubgroup 7 32 where
  rep := fun a => Model.sylowElement (![0, 20, 7, 1, 60, 11, 18, 21, 47, 112, 85, 6, 12, 59, 61, 10, 46, 39, 113, 32, 19, 118, 41, 83, 84, 13, 58, 40, 119, 38, 82, 33] a)
  words := ![[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 0], [3, 4], [4, 0], [0, 1, 0], [0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 3, 4], [1, 0, 2], [1, 2, 3], [1, 2, 4], [1, 3, 0], [1, 4, 0], [2, 3, 4], [3, 0, 4], [0, 1, 0, 2]]
  base := 0
  next := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 19, 20, 21, 22, 16, 18, 14, 23, 15, 10, 11, 12, 13, 17, 31, 28, 27, 26, 25, 30, 29, 24],
    ![2, 10, 0, 11, 12, 13, 23, 24, 22, 21, 1, 3, 4, 5, 25, 26, 27, 19, 28, 17, 30, 9, 8, 6, 7, 14, 15, 16, 18, 31, 20, 29],
    ![3, 7, 11, 0, 14, 15, 20, 1, 16, 18, 24, 2, 25, 26, 4, 5, 8, 29, 9, 31, 6, 28, 27, 30, 10, 12, 13, 22, 21, 17, 23, 19],
    ![4, 16, 13, 14, 0, 17, 27, 8, 7, 30, 28, 26, 19, 2, 3, 29, 1, 5, 23, 12, 22, 24, 20, 18, 21, 31, 11, 6, 10, 15, 9, 25],
    ![5, 18, 12, 15, 17, 0, 28, 9, 30, 7, 27, 25, 2, 19, 29, 3, 23, 4, 1, 13, 21, 20, 24, 16, 22, 11, 31, 10, 6, 14, 8, 26],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  prev := fun j a => (![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 19, 20, 21, 22, 16, 18, 14, 23, 15, 10, 11, 12, 13, 17, 31, 28, 27, 26, 25, 30, 29, 24],
    ![2, 10, 0, 11, 12, 13, 23, 24, 22, 21, 1, 3, 4, 5, 25, 26, 27, 19, 28, 17, 30, 9, 8, 6, 7, 14, 15, 16, 18, 31, 20, 29],
    ![3, 7, 11, 0, 14, 15, 20, 1, 16, 18, 24, 2, 25, 26, 4, 5, 8, 29, 9, 31, 6, 28, 27, 30, 10, 12, 13, 22, 21, 17, 23, 19],
    ![4, 16, 13, 14, 0, 17, 27, 8, 7, 30, 28, 26, 19, 2, 3, 29, 1, 5, 23, 12, 22, 24, 20, 18, 21, 31, 11, 6, 10, 15, 9, 25],
    ![5, 18, 12, 15, 17, 0, 28, 9, 30, 7, 27, 25, 2, 19, 29, 3, 23, 4, 1, 13, 21, 20, 24, 16, 22, 11, 31, 10, 6, 14, 8, 26],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 30, 11, 3, 4, 5, 10, 23, 18, 16, 6, 2, 25, 26, 14, 15, 9, 17, 8, 31, 24, 22, 21, 7, 20, 12, 13, 28, 27, 29, 1, 19]
  unconj := ![0, 30, 11, 3, 4, 5, 10, 23, 18, 16, 6, 2, 25, 26, 14, 15, 9, 17, 8, 31, 24, 22, 21, 7, 20, 12, 13, 28, 27, 29, 1, 19]
  squareRoots := ![[], [6, 8], [8], [], [], [], [6], [6, 8], [6, 8], [6, 8], [6], [8], [8], [8], [], [], [6, 8], [], [6, 8], [8], [6], [6], [6], [6, 8], [6], [8], [8], [6], [6], [], [6, 8], [8]]

private theorem valid27 : cert27.FrattiniValid (generator 27) := by
  decide +kernel

/-- Entry 27 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative27_hasPCoreNormalizerWitness :
    (representative 27).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert27.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 27) valid27

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
