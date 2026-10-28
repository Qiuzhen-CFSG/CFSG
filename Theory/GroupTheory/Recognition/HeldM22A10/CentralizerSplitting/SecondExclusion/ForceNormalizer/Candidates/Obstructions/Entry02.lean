module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 2

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

private def cert2 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 80, 12, 38, 39, 43, 22, 23, 116, 58, 59, 1, 13, 117, 81, 42] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 3], [0, 1, 0], [0, 1, 2], [0, 2, 3], [1, 0, 2]]
  base := 0
  next := fun j a => (![![1, 3, 5, 6, 7, 9, 0, 11, 12, 13, 8, 14, 15, 2, 4, 10],
    ![2, 8, 4, 9, 10, 1, 15, 5, 7, 11, 0, 12, 3, 6, 13, 14],
    ![3, 6, 9, 0, 11, 13, 1, 14, 15, 2, 12, 4, 10, 5, 7, 8],
    ![4, 7, 10, 11, 0, 8, 14, 1, 5, 12, 2, 3, 9, 15, 6, 13],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![6, 0, 13, 1, 14, 2, 3, 4, 10, 5, 15, 7, 8, 9, 11, 12],
    ![10, 5, 0, 12, 2, 7, 13, 8, 1, 3, 4, 9, 11, 14, 15, 6],
    ![3, 6, 9, 0, 11, 13, 1, 14, 15, 2, 12, 4, 10, 5, 7, 8],
    ![4, 7, 10, 11, 0, 8, 14, 1, 5, 12, 2, 3, 9, 15, 6, 13],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 6, 12, 3, 4, 8, 1, 14, 5, 10, 9, 11, 2, 15, 7, 13]
  unconj := ![0, 6, 12, 3, 4, 8, 1, 14, 5, 10, 9, 11, 2, 15, 7, 13]
  squareRoots := ![[], [1], [1, 2], [], [], [2], [1], [1], [2], [1, 2], [1, 2], [], [1, 2], [2], [1], [2]]

private theorem valid2 : cert2.FrattiniValid (generator 2) := by
  decide +kernel

/-- Entry 2 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative2_hasPCoreNormalizerWitness :
    (representative 2).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert2.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 2) valid2

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
