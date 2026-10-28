module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.NormalizerSquareCertificates

/-!
# Outside normalizer witness for second Held entry 10

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

private def cert10 : InvolutionSquareCertificate Model.sylowSubgroup 7 16 where
  rep := fun a => Model.sylowElement (![0, 69, 20, 7, 39, 79, 67, 26, 18, 83, 85, 32, 72, 88, 95, 28] a)
  words := ![[], [0], [1], [2], [3], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 1], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 1], [0, 2, 3]]
  base := 0
  next := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 12, 13, 14, 15, 8, 9, 10, 11],
    ![2, 6, 0, 8, 9, 14, 1, 15, 3, 4, 11, 10, 13, 12, 5, 7],
    ![3, 5, 10, 0, 11, 1, 12, 13, 9, 8, 2, 4, 6, 7, 15, 14],
    ![4, 7, 9, 11, 0, 13, 15, 1, 10, 2, 8, 3, 14, 5, 12, 6],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  prev := fun j a => (![![1, 0, 5, 6, 7, 2, 3, 4, 12, 13, 14, 15, 8, 9, 10, 11],
    ![2, 6, 0, 8, 9, 14, 1, 15, 3, 4, 11, 10, 13, 12, 5, 7],
    ![3, 5, 10, 0, 11, 1, 12, 13, 9, 8, 2, 4, 6, 7, 15, 14],
    ![4, 7, 9, 11, 0, 13, 15, 1, 10, 2, 8, 3, 14, 5, 12, 6],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]) j a
  outside := Model.sylowElement 1
  conj := ![0, 7, 2, 3, 4, 13, 15, 1, 8, 9, 10, 11, 14, 5, 12, 6]
  unconj := ![0, 7, 2, 3, 4, 13, 15, 1, 8, 9, 10, 11, 14, 5, 12, 6]
  squareRoots := ![[], [8], [], [], [], [8], [8], [8], [], [], [], [], [8], [8], [8], [8]]

private theorem valid10 : cert10.FrattiniValid (generator 10) := by
  decide +kernel

/-- Entry 10 has an actual outside Sylow normalizer witness in O₂(Aut(U)). -/
public theorem representative10_hasPCoreNormalizerWitness :
    (representative 10).HasPCoreNormalizerWitness 2 := by
  rw [representative_eq_closure]
  exact cert10.frattini_sound (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card)
    (generator 10) valid10

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.Obstructions
