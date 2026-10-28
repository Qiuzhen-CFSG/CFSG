module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 9

Every displacement is a product of squares, so the action is trivial
on the Frattini quotient. The corresponding kernel is a normal two-subgroup
of the full intrinsic automorphism group. The witness is `Model.element
1`, represented here by its Sylow index 1.

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

private def cert9 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 27, 45, 12, 39, 120, 54, 68, 97, 86, 114, 111, 59, 74, 93, 17] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 0], [2, 3], [0, 1, 2], [1, 0, 1], [1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 4, 5, 6, 7, 10, 12, 0, 3, 13, 11, 2, 8, 15, 9, 14],
    ![2, 8, 4, 9, 10, 14, 1, 6, 7, 12, 0, 13, 15, 5, 11, 3],
    ![3, 11, 9, 4, 12, 1, 14, 5, 13, 10, 15, 7, 0, 6, 8, 2],
    ![4, 7, 10, 12, 0, 11, 8, 1, 6, 15, 2, 5, 3, 14, 13, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![7, 0, 11, 8, 1, 2, 3, 4, 12, 14, 5, 10, 6, 9, 15, 13],
    ![10, 6, 0, 15, 2, 13, 7, 8, 1, 3, 4, 14, 9, 11, 5, 12],
    ![12, 5, 15, 0, 3, 7, 13, 11, 14, 2, 9, 1, 4, 8, 6, 10],
    ![4, 7, 10, 12, 0, 11, 8, 1, 6, 15, 2, 5, 3, 14, 13, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 1
  conj := ![0, 7, 2, 3, 4, 11, 8, 1, 6, 9, 10, 5, 12, 14, 13, 15]
  unconj := ![0, 7, 2, 3, 4, 11, 8, 1, 6, 9, 10, 5, 12, 14, 13, 15]
  squareRoots := ![[], [1], [], [], [], [1], [1], [1], [1], [], [], [1], [], [1], [1], []]

private theorem valid9 : cert9.FrattiniValid (generator 9) := by
  decide +kernel

/-- Entry 9 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative9_hasPCoreNormalizerWitness :
    (representative 9).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert9.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 9) valid9

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
