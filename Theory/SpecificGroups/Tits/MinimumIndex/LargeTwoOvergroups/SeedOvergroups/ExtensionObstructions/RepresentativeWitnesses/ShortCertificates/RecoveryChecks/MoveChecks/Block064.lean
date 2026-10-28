module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 64 through 79

Positive recovery trees and the shared generator equations construct
the actual seed factor for each right transition. Fixed selectors reduce
once, and declarations elaborate sequentially to bound memory.

Source: Parrott (1972), section 5, p.683, and the parent source READMEs.
Reproduce with `RecoveryChecks/source/generate_moves.py`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction

open SylowFactorizationCertificate

set_option Elab.async false

private theorem recovery_check_064 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 64 recoveryData064 j = true := by
  have hg : seedIndices 64 = [11, 16, 65, 128, 513, 1286] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_064 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 64 recoveryData064 rowData064 b j = true := by
  have hi : seedTransversalPattern 64 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData064 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData064 (rowMember rowData064 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData064 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_064 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData064 j b = rowTarget rowData064 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound064 : MoveSound 64 stepData064 :=
  moveSound_of_checks 64 stepData064 recoveryData064 rowData064
    transitionCode transition_checks recovery_check_064 row_check_064 move_target_064

private theorem recovery_check_065 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 65 recoveryData065 j = true := by
  have hg : seedIndices 65 = [11, 16, 65, 128, 515, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_065 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 65 recoveryData065 rowData065 b j = true := by
  have hi : seedTransversalPattern 65 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData065 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData065 (rowMember rowData065 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData065 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_065 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData065 j b = rowTarget rowData065 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound065 : MoveSound 65 stepData065 :=
  moveSound_of_checks 65 stepData065 recoveryData065 rowData065
    transitionCode transition_checks recovery_check_065 row_check_065 move_target_065

private theorem recovery_check_066 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 66 recoveryData066 j = true := by
  have hg : seedIndices 66 = [11, 16, 65, 128, 515, 1285] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_066 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 66 recoveryData066 rowData066 b j = true := by
  have hi : seedTransversalPattern 66 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData066 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData066 (rowMember rowData066 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData066 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_066 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData066 j b = rowTarget rowData066 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound066 : MoveSound 66 stepData066 :=
  moveSound_of_checks 66 stepData066 recoveryData066 rowData066
    transitionCode transition_checks recovery_check_066 row_check_066 move_target_066

private theorem recovery_check_067 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 67 recoveryData067 j = true := by
  have hg : seedIndices 67 = [11, 16, 65, 128, 515, 1286] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_067 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 67 recoveryData067 rowData067 b j = true := by
  have hi : seedTransversalPattern 67 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData067 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData067 (rowMember rowData067 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData067 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_067 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData067 j b = rowTarget rowData067 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound067 : MoveSound 67 stepData067 :=
  moveSound_of_checks 67 stepData067 recoveryData067 rowData067
    transitionCode transition_checks recovery_check_067 row_check_067 move_target_067

private theorem recovery_check_068 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 68 recoveryData068 j = true := by
  have hg : seedIndices 68 = [11, 16, 65, 128, 515, 1287] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_068 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 68 recoveryData068 rowData068 b j = true := by
  have hi : seedTransversalPattern 68 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData068 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData068 (rowMember rowData068 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData068 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_068 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData068 j b = rowTarget rowData068 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound068 : MoveSound 68 stepData068 :=
  moveSound_of_checks 68 stepData068 recoveryData068 rowData068
    transitionCode transition_checks recovery_check_068 row_check_068 move_target_068

private theorem recovery_check_069 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 69 recoveryData069 j = true := by
  have hg : seedIndices 69 = [11, 16, 65, 128, 548, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_069 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 69 recoveryData069 rowData069 b j = true := by
  have hi : seedTransversalPattern 69 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData069 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData069 (rowMember rowData069 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData069 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_069 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData069 j b = rowTarget rowData069 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound069 : MoveSound 69 stepData069 :=
  moveSound_of_checks 69 stepData069 recoveryData069 rowData069
    transitionCode transition_checks recovery_check_069 row_check_069 move_target_069

private theorem recovery_check_070 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 70 recoveryData070 j = true := by
  have hg : seedIndices 70 = [11, 16, 65, 128, 548, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_070 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 70 recoveryData070 rowData070 b j = true := by
  have hi : seedTransversalPattern 70 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData070 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData070 (rowMember rowData070 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData070 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_070 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData070 j b = rowTarget rowData070 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound070 : MoveSound 70 stepData070 :=
  moveSound_of_checks 70 stepData070 recoveryData070 rowData070
    transitionCode transition_checks recovery_check_070 row_check_070 move_target_070

private theorem recovery_check_071 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 71 recoveryData071 j = true := by
  have hg : seedIndices 71 = [11, 16, 65, 128, 550, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_071 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 71 recoveryData071 rowData071 b j = true := by
  have hi : seedTransversalPattern 71 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData071 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData071 (rowMember rowData071 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData071 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_071 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData071 j b = rowTarget rowData071 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound071 : MoveSound 71 stepData071 :=
  moveSound_of_checks 71 stepData071 recoveryData071 rowData071
    transitionCode transition_checks recovery_check_071 row_check_071 move_target_071

private theorem recovery_check_072 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 72 recoveryData072 j = true := by
  have hg : seedIndices 72 = [11, 16, 65, 129, 514, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_072 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 72 recoveryData072 rowData072 b j = true := by
  have hi : seedTransversalPattern 72 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData072 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData072 (rowMember rowData072 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData072 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_072 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData072 j b = rowTarget rowData072 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound072 : MoveSound 72 stepData072 :=
  moveSound_of_checks 72 stepData072 recoveryData072 rowData072
    transitionCode transition_checks recovery_check_072 row_check_072 move_target_072

private theorem recovery_check_073 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 73 recoveryData073 j = true := by
  have hg : seedIndices 73 = [11, 16, 65, 129, 514, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_073 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 73 recoveryData073 rowData073 b j = true := by
  have hi : seedTransversalPattern 73 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData073 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData073 (rowMember rowData073 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData073 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_073 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData073 j b = rowTarget rowData073 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound073 : MoveSound 73 stepData073 :=
  moveSound_of_checks 73 stepData073 recoveryData073 rowData073
    transitionCode transition_checks recovery_check_073 row_check_073 move_target_073

private theorem recovery_check_074 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 74 recoveryData074 j = true := by
  have hg : seedIndices 74 = [11, 16, 65, 164, 515, 1313] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_074 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 74 recoveryData074 rowData074 b j = true := by
  have hi : seedTransversalPattern 74 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData074 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData074 (rowMember rowData074 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData074 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_074 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData074 j b = rowTarget rowData074 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound074 : MoveSound 74 stepData074 :=
  moveSound_of_checks 74 stepData074 recoveryData074 rowData074
    transitionCode transition_checks recovery_check_074 row_check_074 move_target_074

private theorem recovery_check_075 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 75 recoveryData075 j = true := by
  have hg : seedIndices 75 = [11, 16, 65, 164, 515, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_075 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 75 recoveryData075 rowData075 b j = true := by
  have hi : seedTransversalPattern 75 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData075 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData075 (rowMember rowData075 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData075 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_075 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData075 j b = rowTarget rowData075 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound075 : MoveSound 75 stepData075 :=
  moveSound_of_checks 75 stepData075 recoveryData075 rowData075
    transitionCode transition_checks recovery_check_075 row_check_075 move_target_075

private theorem recovery_check_076 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 76 recoveryData076 j = true := by
  have hg : seedIndices 76 = [11, 16, 65, 166, 549, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_076 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 76 recoveryData076 rowData076 b j = true := by
  have hi : seedTransversalPattern 76 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData076 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData076 (rowMember rowData076 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData076 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_076 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData076 j b = rowTarget rowData076 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound076 : MoveSound 76 stepData076 :=
  moveSound_of_checks 76 stepData076 recoveryData076 rowData076
    transitionCode transition_checks recovery_check_076 row_check_076 move_target_076

private theorem recovery_check_077 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 77 recoveryData077 j = true := by
  have hg : seedIndices 77 = [11, 16, 65, 166, 549, 1285] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_077 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 77 recoveryData077 rowData077 b j = true := by
  have hi : seedTransversalPattern 77 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData077 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData077 (rowMember rowData077 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData077 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_077 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData077 j b = rowTarget rowData077 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound077 : MoveSound 77 stepData077 :=
  moveSound_of_checks 77 stepData077 recoveryData077 rowData077
    transitionCode transition_checks recovery_check_077 row_check_077 move_target_077

private theorem recovery_check_078 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 78 recoveryData078 j = true := by
  have hg : seedIndices 78 = [11, 16, 65, 167, 515, 1313] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_078 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 78 recoveryData078 rowData078 b j = true := by
  have hi : seedTransversalPattern 78 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData078 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData078 (rowMember rowData078 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData078 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_078 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData078 j b = rowTarget rowData078 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound078 : MoveSound 78 stepData078 :=
  moveSound_of_checks 78 stepData078 recoveryData078 rowData078
    transitionCode transition_checks recovery_check_078 row_check_078 move_target_078

private theorem recovery_check_079 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 79 recoveryData079 j = true := by
  have hg : seedIndices 79 = [11, 16, 65, 167, 515, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_079 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 79 recoveryData079 rowData079 b j = true := by
  have hi : seedTransversalPattern 79 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData079 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData079 (rowMember rowData079 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData079 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_079 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData079 j b = rowTarget rowData079 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound079 : MoveSound 79 stepData079 :=
  moveSound_of_checks 79 stepData079 recoveryData079 rowData079
    transitionCode transition_checks recovery_check_079 row_check_079 move_target_079


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
