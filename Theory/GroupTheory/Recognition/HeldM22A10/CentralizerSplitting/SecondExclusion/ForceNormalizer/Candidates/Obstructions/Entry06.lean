module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 6

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

private def cert6 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 113, 4, 1, 39, 116, 112, 46, 42, 5, 35, 38, 117, 43, 47, 34] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 0], [1, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]
  base := 0
  next := fun j a => (![![1, 3, 5, 6, 7, 9, 0, 11, 10, 12, 13, 14, 2, 15, 4, 8],
    ![2, 8, 3, 9, 10, 7, 13, 12, 6, 0, 11, 15, 14, 1, 5, 4],
    ![3, 6, 9, 0, 11, 12, 1, 14, 13, 2, 15, 4, 5, 8, 7, 10],
    ![4, 7, 10, 11, 0, 13, 14, 1, 12, 15, 2, 3, 8, 5, 6, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![6, 0, 12, 1, 14, 2, 3, 4, 15, 5, 8, 7, 9, 10, 11, 13],
    ![9, 13, 0, 2, 15, 14, 8, 5, 1, 3, 4, 10, 7, 6, 12, 11],
    ![3, 6, 9, 0, 11, 12, 1, 14, 13, 2, 15, 4, 5, 8, 7, 10],
    ![4, 7, 10, 11, 0, 13, 14, 1, 12, 15, 2, 3, 8, 5, 6, 9],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 2
  conj := ![0, 14, 9, 3, 4, 13, 7, 6, 12, 2, 15, 11, 8, 5, 1, 10]
  unconj := ![0, 14, 9, 3, 4, 13, 7, 6, 12, 2, 15, 11, 8, 5, 1, 10]
  squareRoots := ![[], [5], [1], [], [], [1, 5], [5], [5], [1, 5], [1], [1], [], [1, 5], [1, 5], [5], [1]]

private theorem valid6 : cert6.FrattiniValid (generator 6) := by
  decide +kernel

/-- Entry 6 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative6_hasPCoreNormalizerWitness :
    (representative 6).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert6.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 6) valid6

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
