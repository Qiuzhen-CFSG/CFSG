module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers.Basic
import Mathlib.Tactic.FinCases

/-!
# Certified exact membership in the 23 literal Held nodes

For each original row, the kernel checks that its generators commute and square
to one, and identifies every binary generator product with a literal normal form
using the faithful four-point base. Subgroup closure and product membership then
prove both inclusions. The trivial row is included. Row 8 has redundant generators:
its 128 binary products give precisely the eight members in the unchanged list.

`NodeMembers/Source/generate.py` proposes only the product indices. All identities
and the comparisons with the original 391 listed members are kernel checked here.
No ambient normal-form coverage, order, simplicity, or node normality is assumed.

Source: the retained ATLAS HeG1-p2058B0 model and the original word tables in
`MaximalNormalizerCatalogue/source/` and `IntrinsicEnumeration/source/`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
open LocalPairs.SylowGeometry.Calculations
open NodeMembers

/-- Proposed normal-form indices in binary-product order; repetitions are retained. -/
private def cubeIndices : Option (Fin 22) → List (Fin 1024)
  | none => [0]
  | (some 0) => [0, 512]
  | (some 1) => [0, 512, 368, 880]
  | (some 2) => [0, 512, 144, 656]
  | (some 3) => [0, 512, 992, 480]
  | (some 4) => [0, 512, 96, 608, 368, 880, 784, 272]
  | (some 5) => [0, 512, 896, 384, 368, 880, 752, 240]
  | (some 6) => [0, 512, 992, 480, 144, 656, 368, 880]
  | (some 7) => [0, 512, 992, 480, 976, 464, 48, 560]
  | (some 8) => [0, 992, 480, 512, 832, 672, 160, 320, 672, 832, 320, 160, 992, 0, 512, 480, 320, 160, 672, 832, 512, 480, 992, 0, 480, 512, 0, 992, 160, 320, 832, 672, 160, 320, 832, 672, 480, 512, 0, 992, 512, 480, 992, 0, 320, 160, 672, 832, 992, 0, 512, 480, 672, 832, 320, 160, 832, 672, 160, 320, 0, 992, 480, 512, 512, 480, 992, 0, 320, 160, 672, 832, 160, 320, 832, 672, 480, 512, 0, 992, 832, 672, 160, 320, 0, 992, 480, 512, 992, 0, 512, 480, 672, 832, 320, 160, 672, 832, 320, 160, 992, 0, 512, 480, 0, 992, 480, 512, 832, 672, 160, 320, 480, 512, 0, 992, 160, 320, 832, 672, 320, 160, 672, 832, 512, 480, 992, 0]
  | (some 9) => [0, 512, 96, 608, 368, 880, 784, 272, 162, 674, 706, 194, 978, 466, 946, 434]
  | (some 10) => [0, 512, 896, 384, 368, 880, 752, 240, 2, 514, 898, 386, 370, 882, 754, 242]
  | (some 11) => [0, 512, 992, 480, 976, 464, 48, 560, 258, 770, 226, 738, 722, 210, 818, 306]
  | (some 12) => [0, 512, 992, 480, 144, 656, 368, 880, 1004, 492, 12, 524, 380, 892, 156, 668]
  | (some 13) => [0, 512, 992, 480, 144, 656, 368, 880, 172, 684, 332, 844, 60, 572, 988, 476]
  | (some 14) => [0, 512, 992, 480, 144, 656, 368, 880, 620, 108, 396, 908, 252, 764, 284, 796]
  | (some 15) => [0, 512, 896, 384, 992, 480, 96, 608, 144, 656, 784, 272, 368, 880, 752, 240]
  | (some 16) => [0, 512, 320, 832, 160, 672, 992, 480, 642, 130, 450, 962, 546, 34, 866, 354]
  | (some 17) => [0, 512, 320, 832, 160, 672, 992, 480, 976, 464, 144, 656, 368, 880, 48, 560]
  | (some 18) => [0, 512, 896, 384, 992, 480, 96, 608, 144, 656, 784, 272, 368, 880, 752, 240, 620, 108, 492, 1004, 396, 908, 524, 12, 252, 764, 892, 380, 284, 796, 668, 156]
  | (some 19) => [0, 512, 320, 832, 160, 672, 992, 480, 976, 464, 144, 656, 368, 880, 48, 560, 172, 684, 1004, 492, 12, 524, 332, 844, 380, 892, 60, 572, 988, 476, 156, 668]
  | (some 20) => [0, 512, 896, 384, 992, 480, 96, 608, 144, 656, 784, 272, 368, 880, 752, 240, 620, 108, 492, 1004, 396, 908, 524, 12, 252, 764, 892, 380, 284, 796, 668, 156, 3, 515, 899, 387, 995, 483, 99, 611, 147, 659, 787, 275, 371, 883, 755, 243, 623, 111, 495, 1007, 399, 911, 527, 15, 255, 767, 895, 383, 287, 799, 671, 159]
  | (some _) => [0, 512, 320, 832, 160, 672, 992, 480, 976, 464, 144, 656, 368, 880, 48, 560, 8, 520, 328, 840, 168, 680, 1000, 488, 984, 472, 152, 664, 376, 888, 56, 568, 4, 516, 324, 836, 164, 676, 996, 484, 980, 468, 148, 660, 372, 884, 52, 564, 12, 524, 332, 844, 172, 684, 1004, 492, 988, 476, 156, 668, 380, 892, 60, 572]

private theorem checks_none :
    generatorRelations none = true ∧
    cubeCheck none (cubeIndices none) = true ∧
    (cubeIndices none).toFinset = (members none).toFinset := by
  decide +kernel

private theorem checks_0 :
    generatorRelations (some 0) = true ∧
    cubeCheck (some 0) (cubeIndices (some 0)) = true ∧
    (cubeIndices (some 0)).toFinset = (members (some 0)).toFinset := by
  decide +kernel

private theorem checks_1 :
    generatorRelations (some 1) = true ∧
    cubeCheck (some 1) (cubeIndices (some 1)) = true ∧
    (cubeIndices (some 1)).toFinset = (members (some 1)).toFinset := by
  decide +kernel

private theorem checks_2 :
    generatorRelations (some 2) = true ∧
    cubeCheck (some 2) (cubeIndices (some 2)) = true ∧
    (cubeIndices (some 2)).toFinset = (members (some 2)).toFinset := by
  decide +kernel

private theorem checks_3 :
    generatorRelations (some 3) = true ∧
    cubeCheck (some 3) (cubeIndices (some 3)) = true ∧
    (cubeIndices (some 3)).toFinset = (members (some 3)).toFinset := by
  decide +kernel

private theorem checks_4 :
    generatorRelations (some 4) = true ∧
    cubeCheck (some 4) (cubeIndices (some 4)) = true ∧
    (cubeIndices (some 4)).toFinset = (members (some 4)).toFinset := by
  decide +kernel

private theorem checks_5 :
    generatorRelations (some 5) = true ∧
    cubeCheck (some 5) (cubeIndices (some 5)) = true ∧
    (cubeIndices (some 5)).toFinset = (members (some 5)).toFinset := by
  decide +kernel

private theorem checks_6 :
    generatorRelations (some 6) = true ∧
    cubeCheck (some 6) (cubeIndices (some 6)) = true ∧
    (cubeIndices (some 6)).toFinset = (members (some 6)).toFinset := by
  decide +kernel

private theorem checks_7 :
    generatorRelations (some 7) = true ∧
    cubeCheck (some 7) (cubeIndices (some 7)) = true ∧
    (cubeIndices (some 7)).toFinset = (members (some 7)).toFinset := by
  decide +kernel

private theorem checks_8 :
    generatorRelations (some 8) = true ∧
    cubeCheck (some 8) (cubeIndices (some 8)) = true ∧
    (cubeIndices (some 8)).toFinset = (members (some 8)).toFinset := by
  decide +kernel

private theorem checks_9 :
    generatorRelations (some 9) = true ∧
    cubeCheck (some 9) (cubeIndices (some 9)) = true ∧
    (cubeIndices (some 9)).toFinset = (members (some 9)).toFinset := by
  decide +kernel

private theorem checks_10 :
    generatorRelations (some 10) = true ∧
    cubeCheck (some 10) (cubeIndices (some 10)) = true ∧
    (cubeIndices (some 10)).toFinset = (members (some 10)).toFinset := by
  decide +kernel

private theorem checks_11 :
    generatorRelations (some 11) = true ∧
    cubeCheck (some 11) (cubeIndices (some 11)) = true ∧
    (cubeIndices (some 11)).toFinset = (members (some 11)).toFinset := by
  decide +kernel

private theorem checks_12 :
    generatorRelations (some 12) = true ∧
    cubeCheck (some 12) (cubeIndices (some 12)) = true ∧
    (cubeIndices (some 12)).toFinset = (members (some 12)).toFinset := by
  decide +kernel

private theorem checks_13 :
    generatorRelations (some 13) = true ∧
    cubeCheck (some 13) (cubeIndices (some 13)) = true ∧
    (cubeIndices (some 13)).toFinset = (members (some 13)).toFinset := by
  decide +kernel

private theorem checks_14 :
    generatorRelations (some 14) = true ∧
    cubeCheck (some 14) (cubeIndices (some 14)) = true ∧
    (cubeIndices (some 14)).toFinset = (members (some 14)).toFinset := by
  decide +kernel

private theorem checks_15 :
    generatorRelations (some 15) = true ∧
    cubeCheck (some 15) (cubeIndices (some 15)) = true ∧
    (cubeIndices (some 15)).toFinset = (members (some 15)).toFinset := by
  decide +kernel

private theorem checks_16 :
    generatorRelations (some 16) = true ∧
    cubeCheck (some 16) (cubeIndices (some 16)) = true ∧
    (cubeIndices (some 16)).toFinset = (members (some 16)).toFinset := by
  decide +kernel

private theorem checks_17 :
    generatorRelations (some 17) = true ∧
    cubeCheck (some 17) (cubeIndices (some 17)) = true ∧
    (cubeIndices (some 17)).toFinset = (members (some 17)).toFinset := by
  decide +kernel

private theorem checks_18 :
    generatorRelations (some 18) = true ∧
    cubeCheck (some 18) (cubeIndices (some 18)) = true ∧
    (cubeIndices (some 18)).toFinset = (members (some 18)).toFinset := by
  decide +kernel

private theorem checks_19 :
    generatorRelations (some 19) = true ∧
    cubeCheck (some 19) (cubeIndices (some 19)) = true ∧
    (cubeIndices (some 19)).toFinset = (members (some 19)).toFinset := by
  decide +kernel

private theorem checks_20 :
    generatorRelations (some 20) = true ∧
    cubeCheck (some 20) (cubeIndices (some 20)) = true ∧
    (cubeIndices (some 20)).toFinset = (members (some 20)).toFinset := by
  decide +kernel

private theorem checks_21 :
    generatorRelations (some 21) = true ∧
    cubeCheck (some 21) (cubeIndices (some 21)) = true ∧
    (cubeIndices (some 21)).toFinset = (members (some 21)).toFinset := by
  decide +kernel

private theorem checks (i : Option (Fin 22)) :
    generatorRelations i = true ∧
    cubeCheck i (cubeIndices i) = true ∧
    (cubeIndices i).toFinset = (members i).toFinset := by
  cases i with
  | none => exact checks_none
  | some j =>
    fin_cases j
    · exact checks_0
    · exact checks_1
    · exact checks_2
    · exact checks_3
    · exact checks_4
    · exact checks_5
    · exact checks_6
    · exact checks_7
    · exact checks_8
    · exact checks_9
    · exact checks_10
    · exact checks_11
    · exact checks_12
    · exact checks_13
    · exact checks_14
    · exact checks_15
    · exact checks_16
    · exact checks_17
    · exact checks_18
    · exact checks_19
    · exact checks_20
    · exact checks_21

/-- The literal member lists are exactly the actual subgroups, including bottom. -/
public theorem certified_members (i : Option (Fin 22)) (x : representative) :
    x ∈ node i ↔ ∃ m ∈ members i, normalForm m = x :=
  members_of_checks i (cubeIndices i) (checks i).1 (checks i).2.1 (checks i).2.2 x

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
