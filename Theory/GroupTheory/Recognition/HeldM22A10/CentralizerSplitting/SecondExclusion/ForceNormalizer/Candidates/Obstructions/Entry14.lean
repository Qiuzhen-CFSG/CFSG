module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 14

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

private def cert14 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 80, 4, 1, 39, 38, 84, 81, 23, 5, 35, 22, 34, 85, 19, 18] a)
  words := ![[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [0, 0, 0], [0, 0, 1], [0, 1, 2], [0, 1, 3], [0, 0, 0, 1]]
  base := 0
  next := fun j a => (![![1, 5, 6, 7, 8, 11, 12, 4, 3, 13, 14, 0, 15, 10, 9, 2],
    ![2, 6, 3, 9, 10, 12, 7, 13, 14, 0, 5, 15, 4, 1, 11, 8],
    ![3, 7, 9, 0, 5, 4, 13, 1, 11, 2, 12, 8, 10, 6, 15, 14],
    ![4, 8, 10, 5, 0, 3, 14, 11, 1, 12, 2, 7, 9, 15, 6, 13],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![11, 0, 15, 8, 7, 1, 2, 3, 4, 14, 13, 5, 6, 9, 10, 12],
    ![9, 13, 0, 2, 12, 10, 1, 6, 15, 3, 4, 14, 5, 7, 8, 11],
    ![3, 7, 9, 0, 5, 4, 13, 1, 11, 2, 12, 8, 10, 6, 15, 14],
    ![4, 8, 10, 5, 0, 3, 14, 11, 1, 12, 2, 7, 9, 15, 6, 13],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 11, 9, 3, 4, 5, 14, 8, 7, 2, 12, 1, 10, 15, 6, 13]
  unconj := ![0, 11, 9, 3, 4, 5, 14, 8, 7, 2, 12, 1, 10, 15, 6, 13]
  squareRoots := ![[], [1], [2], [], [], [], [6], [1], [1], [2], [2], [1], [2], [6], [6], [6]]

private theorem valid14 : cert14.FrattiniValid (generator 14) := by
  decide +kernel

/-- Entry 14 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative14_hasPCoreNormalizerWitness :
    (representative 14).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert14.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 14) valid14

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
