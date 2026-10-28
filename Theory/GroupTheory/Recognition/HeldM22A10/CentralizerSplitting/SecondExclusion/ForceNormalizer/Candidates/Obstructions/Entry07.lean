module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 7

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

private def cert7 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 20, 12, 38, 39, 118, 82, 83, 40, 58, 59, 1, 41, 21, 119, 13] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 3], [0, 1, 3], [0, 2, 3], [1, 0, 3], [1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 9, 8, 12, 13, 10, 11, 15, 14],
    ![2, 8, 4, 9, 10, 13, 5, 14, 7, 11, 0, 15, 6, 12, 1, 3],
    ![3, 6, 9, 0, 11, 8, 1, 13, 5, 2, 15, 4, 14, 7, 12, 10],
    ![4, 7, 10, 11, 0, 12, 13, 1, 14, 15, 2, 3, 5, 6, 8, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 9, 8, 12, 13, 10, 11, 15, 14],
    ![10, 14, 0, 15, 2, 6, 12, 8, 1, 3, 4, 9, 13, 5, 7, 11],
    ![3, 6, 9, 0, 11, 8, 1, 13, 5, 2, 15, 4, 14, 7, 12, 10],
    ![4, 7, 10, 11, 0, 12, 13, 1, 14, 15, 2, 3, 5, 6, 8, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 6, 15, 3, 4, 12, 1, 13, 14, 10, 9, 11, 5, 7, 8, 2]
  unconj := ![0, 6, 15, 3, 4, 12, 1, 13, 14, 10, 9, 11, 5, 7, 8, 2]
  squareRoots := ![[], [2, 5], [5], [], [], [2], [2, 5], [2, 5], [2], [5], [5], [], [2], [2, 5], [2], [5]]

private theorem valid7 : cert7.FrattiniValid (generator 7) := by
  decide +kernel

/-- Entry 7 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative7_hasPCoreNormalizerWitness :
    (representative 7).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert7.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 7) valid7

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
