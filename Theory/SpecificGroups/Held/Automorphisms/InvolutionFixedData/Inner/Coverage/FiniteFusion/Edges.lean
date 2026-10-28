module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage.Forest
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Certified edges of the Held involution fusion forest

Each of the 166 nonroot edges is checked on every one of the 2058 letters.
The fixed binary words are expanded once into the already certified two-group
tables. Faithfulness then gives conjugation in the actual Held carrier.

Source: GLS3 Table 5.3p, interpreted on pp.260–261; the candidate forest in
`Coverage/Source/discovery.json`. `FiniteFusion/Source/generate_checks.py`
prints these checks. Only kernel reduction certifies their truth.
-/

namespace Held.InvolutionFixedData.Coverage

set_option Elab.async false

open LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
open TwoLocalCandidates.Cores
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

private def generatorPerm : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | 3 => g3

private theorem generatorPerm_eq (i : Fin 4) :
    generatorPerm i = representation (generator i) := by
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq

private def EdgeEquation (i : Fin 191) : Prop :=
  generatorPerm (forestGenerator i) * normalPerm (forestIndex (forestParent i)) *
    (generatorPerm (forestGenerator i))⁻¹ = normalPerm (forestIndex i)

private theorem normalPerm_expanded (n : Fin 1024) : normalPerm n =
    ([c9 ^ (n.val / 1 % 2), c8 ^ (n.val / 2 % 2),
      c7 ^ (n.val / 4 % 2), c6 ^ (n.val / 8 % 2),
      c5 ^ (n.val / 16 % 2), c4 ^ (n.val / 32 % 2),
      c3 ^ (n.val / 64 % 2), c2 ^ (n.val / 128 % 2),
      c1 ^ (n.val / 256 % 2), c0 ^ (n.val / 512 % 2)] :
      List (Equiv.Perm (Fin 2058))).prod := by
  unfold normalPerm
  apply congrArg List.prod
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_1 : EdgeEquation 1 := by
  unfold EdgeEquation
  rw [show forestGenerator 1 = 1 by decide,
    show forestIndex (forestParent 1) = 2 by decide,
    show forestIndex 1 = 882 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_2 : EdgeEquation 2 := by
  unfold EdgeEquation
  rw [show forestGenerator 2 = 3 by decide,
    show forestIndex (forestParent 2) = 2 by decide,
    show forestIndex 2 = 386 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_3 : EdgeEquation 3 := by
  unfold EdgeEquation
  rw [show forestGenerator 3 = 0 by decide,
    show forestIndex (forestParent 3) = 882 by decide,
    show forestIndex 3 = 370 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_4 : EdgeEquation 4 := by
  unfold EdgeEquation
  rw [show forestGenerator 4 = 3 by decide,
    show forestIndex (forestParent 4) = 882 by decide,
    show forestIndex 4 = 754 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_5 : EdgeEquation 5 := by
  unfold EdgeEquation
  rw [show forestGenerator 5 = 1 by decide,
    show forestIndex (forestParent 5) = 370 by decide,
    show forestIndex 5 = 514 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_6 : EdgeEquation 6 := by
  unfold EdgeEquation
  rw [show forestGenerator 6 = 3 by decide,
    show forestIndex (forestParent 6) = 370 by decide,
    show forestIndex 6 = 242 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_7 : EdgeEquation 7 := by
  unfold EdgeEquation
  rw [show forestGenerator 7 = 3 by decide,
    show forestIndex (forestParent 7) = 514 by decide,
    show forestIndex 7 = 898 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_9 : EdgeEquation 9 := by
  unfold EdgeEquation
  rw [show forestGenerator 9 = 0 by decide,
    show forestIndex (forestParent 9) = 3 by decide,
    show forestIndex 9 = 387 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_10 : EdgeEquation 10 := by
  unfold EdgeEquation
  rw [show forestGenerator 10 = 1 by decide,
    show forestIndex (forestParent 10) = 3 by decide,
    show forestIndex 10 = 15 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_11 : EdgeEquation 11 := by
  unfold EdgeEquation
  rw [show forestGenerator 11 = 1 by decide,
    show forestIndex (forestParent 11) = 387 by decide,
    show forestIndex 11 = 767 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_12 : EdgeEquation 12 := by
  unfold EdgeEquation
  rw [show forestGenerator 12 = 0 by decide,
    show forestIndex (forestParent 12) = 15 by decide,
    show forestIndex 12 = 287 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_13 : EdgeEquation 13 := by
  unfold EdgeEquation
  rw [show forestGenerator 13 = 0 by decide,
    show forestIndex (forestParent 13) = 767 by decide,
    show forestIndex 13 = 1007 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_14 : EdgeEquation 14 := by
  unfold EdgeEquation
  rw [show forestGenerator 14 = 1 by decide,
    show forestIndex (forestParent 14) = 287 by decide,
    show forestIndex 14 = 99 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_15 : EdgeEquation 15 := by
  unfold EdgeEquation
  rw [show forestGenerator 15 = 1 by decide,
    show forestIndex (forestParent 15) = 1007 by decide,
    show forestIndex 15 = 995 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_17 : EdgeEquation 17 := by
  unfold EdgeEquation
  rw [show forestGenerator 17 = 0 by decide,
    show forestIndex (forestParent 17) = 4 by decide,
    show forestIndex 17 = 980 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_18 : EdgeEquation 18 := by
  unfold EdgeEquation
  rw [show forestGenerator 18 = 3 by decide,
    show forestIndex (forestParent 18) = 4 by decide,
    show forestIndex 18 = 8 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_19 : EdgeEquation 19 := by
  unfold EdgeEquation
  rw [show forestGenerator 19 = 3 by decide,
    show forestIndex (forestParent 19) = 980 by decide,
    show forestIndex 19 = 56 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_20 : EdgeEquation 20 := by
  unfold EdgeEquation
  rw [show forestGenerator 20 = 0 by decide,
    show forestIndex (forestParent 20) = 8 by decide,
    show forestIndex 20 = 328 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_21 : EdgeEquation 21 := by
  unfold EdgeEquation
  rw [show forestGenerator 21 = 2 by decide,
    show forestIndex (forestParent 21) = 8 by decide,
    show forestIndex 21 = 888 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_22 : EdgeEquation 22 := by
  unfold EdgeEquation
  rw [show forestGenerator 22 = 3 by decide,
    show forestIndex (forestParent 22) = 8 by decide,
    show forestIndex 22 = 884 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_23 : EdgeEquation 23 := by
  unfold EdgeEquation
  rw [show forestGenerator 23 = 3 by decide,
    show forestIndex (forestParent 23) = 56 by decide,
    show forestIndex 23 = 164 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_25 : EdgeEquation 25 := by
  unfold EdgeEquation
  rw [show forestGenerator 25 = 0 by decide,
    show forestIndex (forestParent 25) = 6 by decide,
    show forestIndex 25 = 982 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_26 : EdgeEquation 26 := by
  unfold EdgeEquation
  rw [show forestGenerator 26 = 1 by decide,
    show forestIndex (forestParent 26) = 6 by decide,
    show forestIndex 26 = 886 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_27 : EdgeEquation 27 := by
  unfold EdgeEquation
  rw [show forestGenerator 27 = 3 by decide,
    show forestIndex (forestParent 27) = 6 by decide,
    show forestIndex 27 = 762 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_28 : EdgeEquation 28 := by
  unfold EdgeEquation
  rw [show forestGenerator 28 = 1 by decide,
    show forestIndex (forestParent 28) = 982 by decide,
    show forestIndex 28 = 678 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_29 : EdgeEquation 29 := by
  unfold EdgeEquation
  rw [show forestGenerator 29 = 3 by decide,
    show forestIndex (forestParent 29) = 982 by decide,
    show forestIndex 29 = 202 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_30 : EdgeEquation 30 := by
  unfold EdgeEquation
  rw [show forestGenerator 30 = 0 by decide,
    show forestIndex (forestParent 30) = 886 by decide,
    show forestIndex 30 = 166 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_31 : EdgeEquation 31 := by
  unfold EdgeEquation
  rw [show forestGenerator 31 = 3 by decide,
    show forestIndex (forestParent 31) = 886 by decide,
    show forestIndex 31 = 394 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_32 : EdgeEquation 32 := by
  unfold EdgeEquation
  rw [show forestGenerator 32 = 0 by decide,
    show forestIndex (forestParent 32) = 762 by decide,
    show forestIndex 32 = 442 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_33 : EdgeEquation 33 := by
  unfold EdgeEquation
  rw [show forestGenerator 33 = 0 by decide,
    show forestIndex (forestParent 33) = 678 by decide,
    show forestIndex 33 = 374 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_34 : EdgeEquation 34 := by
  unfold EdgeEquation
  rw [show forestGenerator 34 = 3 by decide,
    show forestIndex (forestParent 34) = 678 by decide,
    show forestIndex 34 = 954 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_35 : EdgeEquation 35 := by
  unfold EdgeEquation
  rw [show forestGenerator 35 = 1 by decide,
    show forestIndex (forestParent 35) = 166 by decide,
    show forestIndex 35 = 470 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_36 : EdgeEquation 36 := by
  unfold EdgeEquation
  rw [show forestGenerator 36 = 1 by decide,
    show forestIndex (forestParent 36) = 374 by decide,
    show forestIndex 36 = 518 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_37 : EdgeEquation 37 := by
  unfold EdgeEquation
  rw [show forestGenerator 37 = 3 by decide,
    show forestIndex (forestParent 37) = 374 by decide,
    show forestIndex 37 = 906 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_38 : EdgeEquation 38 := by
  unfold EdgeEquation
  rw [show forestGenerator 38 = 0 by decide,
    show forestIndex (forestParent 38) = 954 by decide,
    show forestIndex 38 = 250 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_39 : EdgeEquation 39 := by
  unfold EdgeEquation
  rw [show forestGenerator 39 = 2 by decide,
    show forestIndex (forestParent 39) = 954 by decide,
    show forestIndex 39 = 714 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_41 : EdgeEquation 41 := by
  unfold EdgeEquation
  rw [show forestGenerator 41 = 0 by decide,
    show forestIndex (forestParent 41) = 12 by decide,
    show forestIndex 41 = 156 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_42 : EdgeEquation 42 := by
  unfold EdgeEquation
  rw [show forestGenerator 42 = 2 by decide,
    show forestIndex (forestParent 42) = 12 by decide,
    show forestIndex 42 = 892 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_43 : EdgeEquation 43 := by
  unfold EdgeEquation
  rw [show forestGenerator 43 = 2 by decide,
    show forestIndex (forestParent 43) = 156 by decide,
    show forestIndex 43 = 1004 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_45 : EdgeEquation 45 := by
  unfold EdgeEquation
  rw [show forestGenerator 45 = 1 by decide,
    show forestIndex (forestParent 45) = 16 by decide,
    show forestIndex 45 = 32 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_46 : EdgeEquation 46 := by
  unfold EdgeEquation
  rw [show forestGenerator 46 = 2 by decide,
    show forestIndex (forestParent 46) = 16 by decide,
    show forestIndex 46 = 528 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_47 : EdgeEquation 47 := by
  unfold EdgeEquation
  rw [show forestGenerator 47 = 3 by decide,
    show forestIndex (forestParent 47) = 16 by decide,
    show forestIndex 47 = 912 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_48 : EdgeEquation 48 := by
  unfold EdgeEquation
  rw [show forestGenerator 48 = 0 by decide,
    show forestIndex (forestParent 48) = 32 by decide,
    show forestIndex 48 = 544 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_49 : EdgeEquation 49 := by
  unfold EdgeEquation
  rw [show forestGenerator 49 = 3 by decide,
    show forestIndex (forestParent 49) = 32 by decide,
    show forestIndex 49 = 64 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_50 : EdgeEquation 50 := by
  unfold EdgeEquation
  rw [show forestGenerator 50 = 3 by decide,
    show forestIndex (forestParent 50) = 528 by decide,
    show forestIndex 50 = 400 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_51 : EdgeEquation 51 := by
  unfold EdgeEquation
  rw [show forestGenerator 51 = 1 by decide,
    show forestIndex (forestParent 51) = 912 by decide,
    show forestIndex 51 = 208 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_52 : EdgeEquation 52 := by
  unfold EdgeEquation
  rw [show forestGenerator 52 = 3 by decide,
    show forestIndex (forestParent 52) = 544 by decide,
    show forestIndex 52 = 576 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_53 : EdgeEquation 53 := by
  unfold EdgeEquation
  rw [show forestGenerator 53 = 1 by decide,
    show forestIndex (forestParent 53) = 64 by decide,
    show forestIndex 53 = 256 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_54 : EdgeEquation 54 := by
  unfold EdgeEquation
  rw [show forestGenerator 54 = 1 by decide,
    show forestIndex (forestParent 54) = 400 by decide,
    show forestIndex 54 = 720 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_55 : EdgeEquation 55 := by
  unfold EdgeEquation
  rw [show forestGenerator 55 = 3 by decide,
    show forestIndex (forestParent 55) = 208 by decide,
    show forestIndex 55 = 688 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_56 : EdgeEquation 56 := by
  unfold EdgeEquation
  rw [show forestGenerator 56 = 1 by decide,
    show forestIndex (forestParent 56) = 576 by decide,
    show forestIndex 56 = 768 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_57 : EdgeEquation 57 := by
  unfold EdgeEquation
  rw [show forestGenerator 57 = 3 by decide,
    show forestIndex (forestParent 57) = 256 by decide,
    show forestIndex 57 = 128 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_58 : EdgeEquation 58 := by
  unfold EdgeEquation
  rw [show forestGenerator 58 = 3 by decide,
    show forestIndex (forestParent 58) = 720 by decide,
    show forestIndex 58 = 176 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_59 : EdgeEquation 59 := by
  unfold EdgeEquation
  rw [show forestGenerator 59 = 1 by decide,
    show forestIndex (forestParent 59) = 688 by decide,
    show forestIndex 59 = 640 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_61 : EdgeEquation 61 := by
  unfold EdgeEquation
  rw [show forestGenerator 61 = 0 by decide,
    show forestIndex (forestParent 61) = 34 by decide,
    show forestIndex 61 = 546 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_62 : EdgeEquation 62 := by
  unfold EdgeEquation
  rw [show forestGenerator 62 = 1 by decide,
    show forestIndex (forestParent 62) = 34 by decide,
    show forestIndex 62 = 354 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_63 : EdgeEquation 63 := by
  unfold EdgeEquation
  rw [show forestGenerator 63 = 3 by decide,
    show forestIndex (forestParent 63) = 34 by decide,
    show forestIndex 63 = 962 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_64 : EdgeEquation 64 := by
  unfold EdgeEquation
  rw [show forestGenerator 64 = 1 by decide,
    show forestIndex (forestParent 64) = 546 by decide,
    show forestIndex 64 = 866 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_65 : EdgeEquation 65 := by
  unfold EdgeEquation
  rw [show forestGenerator 65 = 3 by decide,
    show forestIndex (forestParent 65) = 546 by decide,
    show forestIndex 65 = 450 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_66 : EdgeEquation 66 := by
  unfold EdgeEquation
  rw [show forestGenerator 66 = 1 by decide,
    show forestIndex (forestParent 66) = 962 by decide,
    show forestIndex 66 = 130 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_67 : EdgeEquation 67 := by
  unfold EdgeEquation
  rw [show forestGenerator 67 = 1 by decide,
    show forestIndex (forestParent 67) = 450 by decide,
    show forestIndex 67 = 642 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_69 : EdgeEquation 69 := by
  unfold EdgeEquation
  rw [show forestGenerator 69 = 0 by decide,
    show forestIndex (forestParent 69) = 48 by decide,
    show forestIndex 69 = 560 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_70 : EdgeEquation 70 := by
  unfold EdgeEquation
  rw [show forestGenerator 70 = 3 by decide,
    show forestIndex (forestParent 70) = 48 by decide,
    show forestIndex 70 = 464 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_71 : EdgeEquation 71 := by
  unfold EdgeEquation
  rw [show forestGenerator 71 = 3 by decide,
    show forestIndex (forestParent 71) = 560 by decide,
    show forestIndex 71 = 976 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_73 : EdgeEquation 73 := by
  unfold EdgeEquation
  rw [show forestGenerator 73 = 0 by decide,
    show forestIndex (forestParent 73) = 52 by decide,
    show forestIndex 73 = 484 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_74 : EdgeEquation 74 := by
  unfold EdgeEquation
  rw [show forestGenerator 74 = 2 by decide,
    show forestIndex (forestParent 74) = 52 by decide,
    show forestIndex 74 = 564 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_75 : EdgeEquation 75 := by
  unfold EdgeEquation
  rw [show forestGenerator 75 = 3 by decide,
    show forestIndex (forestParent 75) = 52 by decide,
    show forestIndex 75 = 472 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_76 : EdgeEquation 76 := by
  unfold EdgeEquation
  rw [show forestGenerator 76 = 2 by decide,
    show forestIndex (forestParent 76) = 484 by decide,
    show forestIndex 76 = 996 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_77 : EdgeEquation 77 := by
  unfold EdgeEquation
  rw [show forestGenerator 77 = 3 by decide,
    show forestIndex (forestParent 77) = 484 by decide,
    show forestIndex 77 = 1000 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_78 : EdgeEquation 78 := by
  unfold EdgeEquation
  rw [show forestGenerator 78 = 3 by decide,
    show forestIndex (forestParent 78) = 564 by decide,
    show forestIndex 78 = 984 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_79 : EdgeEquation 79 := by
  unfold EdgeEquation
  rw [show forestGenerator 79 = 0 by decide,
    show forestIndex (forestParent 79) = 472 by decide,
    show forestIndex 79 = 664 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_80 : EdgeEquation 80 := by
  unfold EdgeEquation
  rw [show forestGenerator 80 = 2 by decide,
    show forestIndex (forestParent 80) = 472 by decide,
    show forestIndex 80 = 168 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_81 : EdgeEquation 81 := by
  unfold EdgeEquation
  rw [show forestGenerator 81 = 3 by decide,
    show forestIndex (forestParent 81) = 472 by decide,
    show forestIndex 81 = 324 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_82 : EdgeEquation 82 := by
  unfold EdgeEquation
  rw [show forestGenerator 82 = 3 by decide,
    show forestIndex (forestParent 82) = 996 by decide,
    show forestIndex 82 = 488 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_83 : EdgeEquation 83 := by
  unfold EdgeEquation
  rw [show forestGenerator 83 = 0 by decide,
    show forestIndex (forestParent 83) = 1000 by decide,
    show forestIndex 83 = 680 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_84 : EdgeEquation 84 := by
  unfold EdgeEquation
  rw [show forestGenerator 84 = 2 by decide,
    show forestIndex (forestParent 84) = 1000 by decide,
    show forestIndex 84 = 152 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_85 : EdgeEquation 85 := by
  unfold EdgeEquation
  rw [show forestGenerator 85 = 3 by decide,
    show forestIndex (forestParent 85) = 1000 by decide,
    show forestIndex 85 = 148 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_86 : EdgeEquation 86 := by
  unfold EdgeEquation
  rw [show forestGenerator 86 = 3 by decide,
    show forestIndex (forestParent 86) = 984 by decide,
    show forestIndex 86 = 836 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_87 : EdgeEquation 87 := by
  unfold EdgeEquation
  rw [show forestGenerator 87 = 3 by decide,
    show forestIndex (forestParent 87) = 488 by decide,
    show forestIndex 87 = 660 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_89 : EdgeEquation 89 := by
  unfold EdgeEquation
  rw [show forestGenerator 89 = 0 by decide,
    show forestIndex (forestParent 89) = 60 by decide,
    show forestIndex 89 = 684 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_90 : EdgeEquation 90 := by
  unfold EdgeEquation
  rw [show forestGenerator 90 = 2 by decide,
    show forestIndex (forestParent 90) = 60 by decide,
    show forestIndex 90 = 332 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_91 : EdgeEquation 91 := by
  unfold EdgeEquation
  rw [show forestGenerator 91 = 3 by decide,
    show forestIndex (forestParent 91) = 60 by decide,
    show forestIndex 91 = 172 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_92 : EdgeEquation 92 := by
  unfold EdgeEquation
  rw [show forestGenerator 92 = 2 by decide,
    show forestIndex (forestParent 92) = 684 by decide,
    show forestIndex 92 = 988 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_93 : EdgeEquation 93 := by
  unfold EdgeEquation
  rw [show forestGenerator 93 = 0 by decide,
    show forestIndex (forestParent 93) = 172 by decide,
    show forestIndex 93 = 572 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_94 : EdgeEquation 94 := by
  unfold EdgeEquation
  rw [show forestGenerator 94 = 2 by decide,
    show forestIndex (forestParent 94) = 172 by decide,
    show forestIndex 94 = 476 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_95 : EdgeEquation 95 := by
  unfold EdgeEquation
  rw [show forestGenerator 95 = 3 by decide,
    show forestIndex (forestParent 95) = 988 by decide,
    show forestIndex 95 = 844 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_97 : EdgeEquation 97 := by
  unfold EdgeEquation
  rw [show forestGenerator 97 = 0 by decide,
    show forestIndex (forestParent 97) = 77 by decide,
    show forestIndex 97 = 349 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_98 : EdgeEquation 98 := by
  unfold EdgeEquation
  rw [show forestGenerator 98 = 1 by decide,
    show forestIndex (forestParent 98) = 77 by decide,
    show forestIndex 98 = 257 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_99 : EdgeEquation 99 := by
  unfold EdgeEquation
  rw [show forestGenerator 99 = 2 by decide,
    show forestIndex (forestParent 99) = 77 by decide,
    show forestIndex 99 = 701 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_100 : EdgeEquation 100 := by
  unfold EdgeEquation
  rw [show forestGenerator 100 = 3 by decide,
    show forestIndex (forestParent 100) = 77 by decide,
    show forestIndex 100 = 861 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_101 : EdgeEquation 101 := by
  unfold EdgeEquation
  rw [show forestGenerator 101 = 1 by decide,
    show forestIndex (forestParent 101) = 349 by decide,
    show forestIndex 101 = 353 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_102 : EdgeEquation 102 := by
  unfold EdgeEquation
  rw [show forestGenerator 102 = 2 by decide,
    show forestIndex (forestParent 102) = 349 by decide,
    show forestIndex 102 = 941 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_103 : EdgeEquation 103 := by
  unfold EdgeEquation
  rw [show forestGenerator 103 = 0 by decide,
    show forestIndex (forestParent 103) = 257 by decide,
    show forestIndex 103 = 129 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_104 : EdgeEquation 104 := by
  unfold EdgeEquation
  rw [show forestGenerator 104 = 1 by decide,
    show forestIndex (forestParent 104) = 701 by decide,
    show forestIndex 104 = 641 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_105 : EdgeEquation 105 := by
  unfold EdgeEquation
  rw [show forestGenerator 105 = 0 by decide,
    show forestIndex (forestParent 105) = 861 by decide,
    show forestIndex 105 = 589 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_106 : EdgeEquation 106 := by
  unfold EdgeEquation
  rw [show forestGenerator 106 = 1 by decide,
    show forestIndex (forestParent 106) = 861 by decide,
    show forestIndex 106 = 865 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_107 : EdgeEquation 107 := by
  unfold EdgeEquation
  rw [show forestGenerator 107 = 2 by decide,
    show forestIndex (forestParent 107) = 861 by decide,
    show forestIndex 107 = 429 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_108 : EdgeEquation 108 := by
  unfold EdgeEquation
  rw [show forestGenerator 108 = 0 by decide,
    show forestIndex (forestParent 108) = 353 by decide,
    show forestIndex 108 = 737 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_109 : EdgeEquation 109 := by
  unfold EdgeEquation
  rw [show forestGenerator 109 = 1 by decide,
    show forestIndex (forestParent 109) = 941 by decide,
    show forestIndex 109 = 225 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_110 : EdgeEquation 110 := by
  unfold EdgeEquation
  rw [show forestGenerator 110 = 3 by decide,
    show forestIndex (forestParent 110) = 941 by decide,
    show forestIndex 110 = 189 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_111 : EdgeEquation 111 := by
  unfold EdgeEquation
  rw [show forestGenerator 111 = 0 by decide,
    show forestIndex (forestParent 111) = 641 by decide,
    show forestIndex 111 = 769 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_113 : EdgeEquation 113 := by
  unfold EdgeEquation
  rw [show forestGenerator 113 = 0 by decide,
    show forestIndex (forestParent 113) = 96 by decide,
    show forestIndex 113 = 608 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_114 : EdgeEquation 114 := by
  unfold EdgeEquation
  rw [show forestGenerator 114 = 1 by decide,
    show forestIndex (forestParent 114) = 96 by decide,
    show forestIndex 114 = 272 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_115 : EdgeEquation 115 := by
  unfold EdgeEquation
  rw [show forestGenerator 115 = 1 by decide,
    show forestIndex (forestParent 115) = 608 by decide,
    show forestIndex 115 = 784 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_117 : EdgeEquation 117 := by
  unfold EdgeEquation
  rw [show forestGenerator 117 = 0 by decide,
    show forestIndex (forestParent 117) = 108 by decide,
    show forestIndex 117 = 252 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_118 : EdgeEquation 118 := by
  unfold EdgeEquation
  rw [show forestGenerator 118 = 1 by decide,
    show forestIndex (forestParent 118) = 108 by decide,
    show forestIndex 118 = 284 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_119 : EdgeEquation 119 := by
  unfold EdgeEquation
  rw [show forestGenerator 119 = 2 by decide,
    show forestIndex (forestParent 119) = 108 by decide,
    show forestIndex 119 = 796 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_120 : EdgeEquation 120 := by
  unfold EdgeEquation
  rw [show forestGenerator 120 = 1 by decide,
    show forestIndex (forestParent 120) = 252 by decide,
    show forestIndex 120 = 908 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_121 : EdgeEquation 121 := by
  unfold EdgeEquation
  rw [show forestGenerator 121 = 0 by decide,
    show forestIndex (forestParent 121) = 284 by decide,
    show forestIndex 121 = 396 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_122 : EdgeEquation 122 := by
  unfold EdgeEquation
  rw [show forestGenerator 122 = 2 by decide,
    show forestIndex (forestParent 122) = 284 by decide,
    show forestIndex 122 = 620 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_123 : EdgeEquation 123 := by
  unfold EdgeEquation
  rw [show forestGenerator 123 = 1 by decide,
    show forestIndex (forestParent 123) = 396 by decide,
    show forestIndex 123 = 764 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_125 : EdgeEquation 125 := by
  unfold EdgeEquation
  rw [show forestGenerator 125 = 0 by decide,
    show forestIndex (forestParent 125) = 111 by decide,
    show forestIndex 125 = 383 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_126 : EdgeEquation 126 := by
  unfold EdgeEquation
  rw [show forestGenerator 126 = 1 by decide,
    show forestIndex (forestParent 126) = 111 by decide,
    show forestIndex 126 = 275 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_127 : EdgeEquation 127 := by
  unfold EdgeEquation
  rw [show forestGenerator 127 = 2 by decide,
    show forestIndex (forestParent 127) = 111 by decide,
    show forestIndex 127 = 671 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_128 : EdgeEquation 128 := by
  unfold EdgeEquation
  rw [show forestGenerator 128 = 1 by decide,
    show forestIndex (forestParent 128) = 383 by decide,
    show forestIndex 128 = 371 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_129 : EdgeEquation 129 := by
  unfold EdgeEquation
  rw [show forestGenerator 129 = 2 by decide,
    show forestIndex (forestParent 129) = 383 by decide,
    show forestIndex 129 = 911 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_130 : EdgeEquation 130 := by
  unfold EdgeEquation
  rw [show forestGenerator 130 = 0 by decide,
    show forestIndex (forestParent 130) = 275 by decide,
    show forestIndex 130 = 147 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_131 : EdgeEquation 131 := by
  unfold EdgeEquation
  rw [show forestGenerator 131 = 2 by decide,
    show forestIndex (forestParent 131) = 275 by decide,
    show forestIndex 131 = 659 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_132 : EdgeEquation 132 := by
  unfold EdgeEquation
  rw [show forestGenerator 132 = 0 by decide,
    show forestIndex (forestParent 132) = 371 by decide,
    show forestIndex 132 = 755 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_133 : EdgeEquation 133 := by
  unfold EdgeEquation
  rw [show forestGenerator 133 = 2 by decide,
    show forestIndex (forestParent 133) = 371 by decide,
    show forestIndex 133 = 243 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_134 : EdgeEquation 134 := by
  unfold EdgeEquation
  rw [show forestGenerator 134 = 1 by decide,
    show forestIndex (forestParent 134) = 147 by decide,
    show forestIndex 134 = 159 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_135 : EdgeEquation 135 := by
  unfold EdgeEquation
  rw [show forestGenerator 135 = 2 by decide,
    show forestIndex (forestParent 135) = 147 by decide,
    show forestIndex 135 = 787 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_136 : EdgeEquation 136 := by
  unfold EdgeEquation
  rw [show forestGenerator 136 = 1 by decide,
    show forestIndex (forestParent 136) = 755 by decide,
    show forestIndex 136 = 399 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_137 : EdgeEquation 137 := by
  unfold EdgeEquation
  rw [show forestGenerator 137 = 2 by decide,
    show forestIndex (forestParent 137) = 755 by decide,
    show forestIndex 137 = 883 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_138 : EdgeEquation 138 := by
  unfold EdgeEquation
  rw [show forestGenerator 138 = 2 by decide,
    show forestIndex (forestParent 138) = 159 by decide,
    show forestIndex 138 = 623 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_139 : EdgeEquation 139 := by
  unfold EdgeEquation
  rw [show forestGenerator 139 = 2 by decide,
    show forestIndex (forestParent 139) = 399 by decide,
    show forestIndex 139 = 895 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_141 : EdgeEquation 141 := by
  unfold EdgeEquation
  rw [show forestGenerator 141 = 2 by decide,
    show forestIndex (forestParent 141) = 144 by decide,
    show forestIndex 141 = 656 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_143 : EdgeEquation 143 := by
  unfold EdgeEquation
  rw [show forestGenerator 143 = 0 by decide,
    show forestIndex (forestParent 143) = 160 by decide,
    show forestIndex 143 = 672 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_144 : EdgeEquation 144 := by
  unfold EdgeEquation
  rw [show forestGenerator 144 = 3 by decide,
    show forestIndex (forestParent 144) = 160 by decide,
    show forestIndex 144 = 320 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_145 : EdgeEquation 145 := by
  unfold EdgeEquation
  rw [show forestGenerator 145 = 3 by decide,
    show forestIndex (forestParent 145) = 672 by decide,
    show forestIndex 145 = 832 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_147 : EdgeEquation 147 := by
  unfold EdgeEquation
  rw [show forestGenerator 147 = 0 by decide,
    show forestIndex (forestParent 147) = 162 by decide,
    show forestIndex 147 = 674 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_148 : EdgeEquation 148 := by
  unfold EdgeEquation
  rw [show forestGenerator 148 = 1 by decide,
    show forestIndex (forestParent 148) = 162 by decide,
    show forestIndex 148 = 466 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_149 : EdgeEquation 149 := by
  unfold EdgeEquation
  rw [show forestGenerator 149 = 3 by decide,
    show forestIndex (forestParent 149) = 162 by decide,
    show forestIndex 149 = 706 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_150 : EdgeEquation 150 := by
  unfold EdgeEquation
  rw [show forestGenerator 150 = 1 by decide,
    show forestIndex (forestParent 150) = 674 by decide,
    show forestIndex 150 = 978 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_151 : EdgeEquation 151 := by
  unfold EdgeEquation
  rw [show forestGenerator 151 = 3 by decide,
    show forestIndex (forestParent 151) = 674 by decide,
    show forestIndex 151 = 194 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_152 : EdgeEquation 152 := by
  unfold EdgeEquation
  rw [show forestGenerator 152 = 3 by decide,
    show forestIndex (forestParent 152) = 466 by decide,
    show forestIndex 152 = 434 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_153 : EdgeEquation 153 := by
  unfold EdgeEquation
  rw [show forestGenerator 153 = 3 by decide,
    show forestIndex (forestParent 153) = 978 by decide,
    show forestIndex 153 = 946 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_155 : EdgeEquation 155 := by
  unfold EdgeEquation
  rw [show forestGenerator 155 = 1 by decide,
    show forestIndex (forestParent 155) = 210 by decide,
    show forestIndex 155 = 738 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_156 : EdgeEquation 156 := by
  unfold EdgeEquation
  rw [show forestGenerator 156 = 3 by decide,
    show forestIndex (forestParent 156) = 210 by decide,
    show forestIndex 156 = 306 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_157 : EdgeEquation 157 := by
  unfold EdgeEquation
  rw [show forestGenerator 157 = 0 by decide,
    show forestIndex (forestParent 157) = 738 by decide,
    show forestIndex 157 = 226 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_158 : EdgeEquation 158 := by
  unfold EdgeEquation
  rw [show forestGenerator 158 = 0 by decide,
    show forestIndex (forestParent 158) = 306 by decide,
    show forestIndex 158 = 818 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_159 : EdgeEquation 159 := by
  unfold EdgeEquation
  rw [show forestGenerator 159 = 1 by decide,
    show forestIndex (forestParent 159) = 306 by decide,
    show forestIndex 159 = 770 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_160 : EdgeEquation 160 := by
  unfold EdgeEquation
  rw [show forestGenerator 160 = 3 by decide,
    show forestIndex (forestParent 160) = 306 by decide,
    show forestIndex 160 = 722 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_161 : EdgeEquation 161 := by
  unfold EdgeEquation
  rw [show forestGenerator 161 = 1 by decide,
    show forestIndex (forestParent 161) = 818 by decide,
    show forestIndex 161 = 258 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_163 : EdgeEquation 163 := by
  unfold EdgeEquation
  rw [show forestGenerator 163 = 0 by decide,
    show forestIndex (forestParent 163) = 240 by decide,
    show forestIndex 163 = 752 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_164 : EdgeEquation 164 := by
  unfold EdgeEquation
  rw [show forestGenerator 164 = 1 by decide,
    show forestIndex (forestParent 164) = 240 by decide,
    show forestIndex 164 = 896 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_165 : EdgeEquation 165 := by
  unfold EdgeEquation
  rw [show forestGenerator 165 = 1 by decide,
    show forestIndex (forestParent 165) = 752 by decide,
    show forestIndex 165 = 384 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_167 : EdgeEquation 167 := by
  unfold EdgeEquation
  rw [show forestGenerator 167 = 0 by decide,
    show forestIndex (forestParent 167) = 255 by decide,
    show forestIndex 167 = 495 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_168 : EdgeEquation 168 := by
  unfold EdgeEquation
  rw [show forestGenerator 168 = 1 by decide,
    show forestIndex (forestParent 168) = 255 by decide,
    show forestIndex 168 = 899 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_169 : EdgeEquation 169 := by
  unfold EdgeEquation
  rw [show forestGenerator 169 = 2 by decide,
    show forestIndex (forestParent 169) = 255 by decide,
    show forestIndex 169 = 527 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_170 : EdgeEquation 170 := by
  unfold EdgeEquation
  rw [show forestGenerator 170 = 1 by decide,
    show forestIndex (forestParent 170) = 495 by decide,
    show forestIndex 170 = 483 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_171 : EdgeEquation 171 := by
  unfold EdgeEquation
  rw [show forestGenerator 171 = 2 by decide,
    show forestIndex (forestParent 171) = 495 by decide,
    show forestIndex 171 = 799 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_172 : EdgeEquation 172 := by
  unfold EdgeEquation
  rw [show forestGenerator 172 = 0 by decide,
    show forestIndex (forestParent 172) = 899 by decide,
    show forestIndex 172 = 515 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_173 : EdgeEquation 173 := by
  unfold EdgeEquation
  rw [show forestGenerator 173 = 0 by decide,
    show forestIndex (forestParent 173) = 483 by decide,
    show forestIndex 173 = 611 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_175 : EdgeEquation 175 := by
  unfold EdgeEquation
  rw [show forestGenerator 175 = 0 by decide,
    show forestIndex (forestParent 175) = 368 by decide,
    show forestIndex 175 = 880 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_177 : EdgeEquation 177 := by
  unfold EdgeEquation
  rw [show forestGenerator 177 = 0 by decide,
    show forestIndex (forestParent 177) = 372 by decide,
    show forestIndex 177 = 676 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_178 : EdgeEquation 178 := by
  unfold EdgeEquation
  rw [show forestGenerator 178 = 3 by decide,
    show forestIndex (forestParent 178) = 372 by decide,
    show forestIndex 178 = 376 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_179 : EdgeEquation 179 := by
  unfold EdgeEquation
  rw [show forestGenerator 179 = 3 by decide,
    show forestIndex (forestParent 179) = 676 by decide,
    show forestIndex 179 = 840 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_180 : EdgeEquation 180 := by
  unfold EdgeEquation
  rw [show forestGenerator 180 = 0 by decide,
    show forestIndex (forestParent 180) = 376 by decide,
    show forestIndex 180 = 568 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_181 : EdgeEquation 181 := by
  unfold EdgeEquation
  rw [show forestGenerator 181 = 2 by decide,
    show forestIndex (forestParent 181) = 376 by decide,
    show forestIndex 181 = 520 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_182 : EdgeEquation 182 := by
  unfold EdgeEquation
  rw [show forestGenerator 182 = 3 by decide,
    show forestIndex (forestParent 182) = 376 by decide,
    show forestIndex 182 = 516 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_183 : EdgeEquation 183 := by
  unfold EdgeEquation
  rw [show forestGenerator 183 = 3 by decide,
    show forestIndex (forestParent 183) = 840 by decide,
    show forestIndex 183 = 468 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_185 : EdgeEquation 185 := by
  unfold EdgeEquation
  rw [show forestGenerator 185 = 0 by decide,
    show forestIndex (forestParent 185) = 380 by decide,
    show forestIndex 185 = 492 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_186 : EdgeEquation 186 := by
  unfold EdgeEquation
  rw [show forestGenerator 186 = 2 by decide,
    show forestIndex (forestParent 186) = 380 by decide,
    show forestIndex 186 = 524 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_187 : EdgeEquation 187 := by
  unfold EdgeEquation
  rw [show forestGenerator 187 = 2 by decide,
    show forestIndex (forestParent 187) = 492 by decide,
    show forestIndex 187 = 668 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_189 : EdgeEquation 189 := by
  unfold EdgeEquation
  rw [show forestGenerator 189 = 0 by decide,
    show forestIndex (forestParent 189) = 480 by decide,
    show forestIndex 189 = 992 by decide,
    normalPerm_expanded, normalPerm_expanded]
  norm_num [generatorPerm]
  apply Equiv.ext
  apply allLetters
  decide +kernel

/-- Every nonroot forest edge is the stated conjugation in Held. -/
public theorem forest_edge_identity (i : Fin 191)
    (hi : (forestParent i).val < i.val) :
    MulAut.conj (generator (forestGenerator i))
        (normalForm (forestIndex (forestParent i))).val =
      (normalForm (forestIndex i)).val := by
  have h : EdgeEquation i := by
    fin_cases i
    · exact False.elim ((by decide : ¬ (forestParent 0).val < (0 : Fin 191).val) hi)
    · exact edge_1
    · exact edge_2
    · exact edge_3
    · exact edge_4
    · exact edge_5
    · exact edge_6
    · exact edge_7
    · exact False.elim ((by decide : ¬ (forestParent 8).val < (8 : Fin 191).val) hi)
    · exact edge_9
    · exact edge_10
    · exact edge_11
    · exact edge_12
    · exact edge_13
    · exact edge_14
    · exact edge_15
    · exact False.elim ((by decide : ¬ (forestParent 16).val < (16 : Fin 191).val) hi)
    · exact edge_17
    · exact edge_18
    · exact edge_19
    · exact edge_20
    · exact edge_21
    · exact edge_22
    · exact edge_23
    · exact False.elim ((by decide : ¬ (forestParent 24).val < (24 : Fin 191).val) hi)
    · exact edge_25
    · exact edge_26
    · exact edge_27
    · exact edge_28
    · exact edge_29
    · exact edge_30
    · exact edge_31
    · exact edge_32
    · exact edge_33
    · exact edge_34
    · exact edge_35
    · exact edge_36
    · exact edge_37
    · exact edge_38
    · exact edge_39
    · exact False.elim ((by decide : ¬ (forestParent 40).val < (40 : Fin 191).val) hi)
    · exact edge_41
    · exact edge_42
    · exact edge_43
    · exact False.elim ((by decide : ¬ (forestParent 44).val < (44 : Fin 191).val) hi)
    · exact edge_45
    · exact edge_46
    · exact edge_47
    · exact edge_48
    · exact edge_49
    · exact edge_50
    · exact edge_51
    · exact edge_52
    · exact edge_53
    · exact edge_54
    · exact edge_55
    · exact edge_56
    · exact edge_57
    · exact edge_58
    · exact edge_59
    · exact False.elim ((by decide : ¬ (forestParent 60).val < (60 : Fin 191).val) hi)
    · exact edge_61
    · exact edge_62
    · exact edge_63
    · exact edge_64
    · exact edge_65
    · exact edge_66
    · exact edge_67
    · exact False.elim ((by decide : ¬ (forestParent 68).val < (68 : Fin 191).val) hi)
    · exact edge_69
    · exact edge_70
    · exact edge_71
    · exact False.elim ((by decide : ¬ (forestParent 72).val < (72 : Fin 191).val) hi)
    · exact edge_73
    · exact edge_74
    · exact edge_75
    · exact edge_76
    · exact edge_77
    · exact edge_78
    · exact edge_79
    · exact edge_80
    · exact edge_81
    · exact edge_82
    · exact edge_83
    · exact edge_84
    · exact edge_85
    · exact edge_86
    · exact edge_87
    · exact False.elim ((by decide : ¬ (forestParent 88).val < (88 : Fin 191).val) hi)
    · exact edge_89
    · exact edge_90
    · exact edge_91
    · exact edge_92
    · exact edge_93
    · exact edge_94
    · exact edge_95
    · exact False.elim ((by decide : ¬ (forestParent 96).val < (96 : Fin 191).val) hi)
    · exact edge_97
    · exact edge_98
    · exact edge_99
    · exact edge_100
    · exact edge_101
    · exact edge_102
    · exact edge_103
    · exact edge_104
    · exact edge_105
    · exact edge_106
    · exact edge_107
    · exact edge_108
    · exact edge_109
    · exact edge_110
    · exact edge_111
    · exact False.elim ((by decide : ¬ (forestParent 112).val < (112 : Fin 191).val) hi)
    · exact edge_113
    · exact edge_114
    · exact edge_115
    · exact False.elim ((by decide : ¬ (forestParent 116).val < (116 : Fin 191).val) hi)
    · exact edge_117
    · exact edge_118
    · exact edge_119
    · exact edge_120
    · exact edge_121
    · exact edge_122
    · exact edge_123
    · exact False.elim ((by decide : ¬ (forestParent 124).val < (124 : Fin 191).val) hi)
    · exact edge_125
    · exact edge_126
    · exact edge_127
    · exact edge_128
    · exact edge_129
    · exact edge_130
    · exact edge_131
    · exact edge_132
    · exact edge_133
    · exact edge_134
    · exact edge_135
    · exact edge_136
    · exact edge_137
    · exact edge_138
    · exact edge_139
    · exact False.elim ((by decide : ¬ (forestParent 140).val < (140 : Fin 191).val) hi)
    · exact edge_141
    · exact False.elim ((by decide : ¬ (forestParent 142).val < (142 : Fin 191).val) hi)
    · exact edge_143
    · exact edge_144
    · exact edge_145
    · exact False.elim ((by decide : ¬ (forestParent 146).val < (146 : Fin 191).val) hi)
    · exact edge_147
    · exact edge_148
    · exact edge_149
    · exact edge_150
    · exact edge_151
    · exact edge_152
    · exact edge_153
    · exact False.elim ((by decide : ¬ (forestParent 154).val < (154 : Fin 191).val) hi)
    · exact edge_155
    · exact edge_156
    · exact edge_157
    · exact edge_158
    · exact edge_159
    · exact edge_160
    · exact edge_161
    · exact False.elim ((by decide : ¬ (forestParent 162).val < (162 : Fin 191).val) hi)
    · exact edge_163
    · exact edge_164
    · exact edge_165
    · exact False.elim ((by decide : ¬ (forestParent 166).val < (166 : Fin 191).val) hi)
    · exact edge_167
    · exact edge_168
    · exact edge_169
    · exact edge_170
    · exact edge_171
    · exact edge_172
    · exact edge_173
    · exact False.elim ((by decide : ¬ (forestParent 174).val < (174 : Fin 191).val) hi)
    · exact edge_175
    · exact False.elim ((by decide : ¬ (forestParent 176).val < (176 : Fin 191).val) hi)
    · exact edge_177
    · exact edge_178
    · exact edge_179
    · exact edge_180
    · exact edge_181
    · exact edge_182
    · exact edge_183
    · exact False.elim ((by decide : ¬ (forestParent 184).val < (184 : Fin 191).val) hi)
    · exact edge_185
    · exact edge_186
    · exact edge_187
    · exact False.elim ((by decide : ¬ (forestParent 188).val < (188 : Fin 191).val) hi)
    · exact edge_189
    · exact False.elim ((by decide : ¬ (forestParent 190).val < (190 : Fin 191).val) hi)
  apply representation_injective
  simpa only [EdgeEquation, MulAut.conj_apply, map_mul, map_inv, normalForm_representation,
    ← generatorPerm_eq] using h

end Held.InvolutionFixedData.Coverage
