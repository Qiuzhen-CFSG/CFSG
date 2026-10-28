module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 96 through 111

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

private theorem recovery_check_096 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 96 recoveryData096 j = true := by
  have hg : seedIndices 96 = [16, 37, 139, 260] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_096 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 96 recoveryData096 rowData096 b j = true := by
  have hi : seedTransversalPattern 96 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData096 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData096 (rowMember rowData096 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData096 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_096 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData096 j b = rowTarget rowData096 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound096 : MoveSound 96 stepData096 :=
  moveSound_of_checks 96 stepData096 recoveryData096 rowData096
    transitionCode transition_checks recovery_check_096 row_check_096 move_target_096

private theorem recovery_check_097 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 97 recoveryData097 j = true := by
  have hg : seedIndices 97 = [16, 37, 139, 271] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_097 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 97 recoveryData097 rowData097 b j = true := by
  have hi : seedTransversalPattern 97 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData097 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData097 (rowMember rowData097 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData097 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_097 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData097 j b = rowTarget rowData097 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound097 : MoveSound 97 stepData097 :=
  moveSound_of_checks 97 stepData097 recoveryData097 rowData097
    transitionCode transition_checks recovery_check_097 row_check_097 move_target_097

private theorem recovery_check_098 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 98 recoveryData098 j = true := by
  have hg : seedIndices 98 = [16, 46, 128, 522, 1286] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_098 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 98 recoveryData098 rowData098 b j = true := by
  have hi : seedTransversalPattern 98 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData098 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData098 (rowMember rowData098 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData098 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_098 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData098 j b = rowTarget rowData098 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound098 : MoveSound 98 stepData098 :=
  moveSound_of_checks 98 stepData098 recoveryData098 rowData098
    transitionCode transition_checks recovery_check_098 row_check_098 move_target_098

private theorem recovery_check_099 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 99 recoveryData099 j = true := by
  have hg : seedIndices 99 = [16, 65, 128, 288, 1026] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_099 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 99 recoveryData099 rowData099 b j = true := by
  have hi : seedTransversalPattern 99 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData099 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData099 (rowMember rowData099 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData099 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_099 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData099 j b = rowTarget rowData099 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound099 : MoveSound 99 stepData099 :=
  moveSound_of_checks 99 stepData099 recoveryData099 rowData099
    transitionCode transition_checks recovery_check_099 row_check_099 move_target_099

private theorem recovery_check_100 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 100 recoveryData100 j = true := by
  have hg : seedIndices 100 = [16, 65, 128, 290, 1024] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_100 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 100 recoveryData100 rowData100 b j = true := by
  have hi : seedTransversalPattern 100 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData100 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData100 (rowMember rowData100 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData100 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_100 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData100 j b = rowTarget rowData100 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound100 : MoveSound 100 stepData100 :=
  moveSound_of_checks 100 stepData100 recoveryData100 rowData100
    transitionCode transition_checks recovery_check_100 row_check_100 move_target_100

private theorem recovery_check_101 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 101 recoveryData101 j = true := by
  have hg : seedIndices 101 = [16, 65, 128, 297, 1035] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_101 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 101 recoveryData101 rowData101 b j = true := by
  have hi : seedTransversalPattern 101 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData101 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData101 (rowMember rowData101 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData101 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_101 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData101 j b = rowTarget rowData101 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound101 : MoveSound 101 stepData101 :=
  moveSound_of_checks 101 stepData101 recoveryData101 rowData101
    transitionCode transition_checks recovery_check_101 row_check_101 move_target_101

private theorem recovery_check_102 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 102 recoveryData102 j = true := by
  have hg : seedIndices 102 = [16, 65, 139, 260, 1068] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_102 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 102 recoveryData102 rowData102 b j = true := by
  have hi : seedTransversalPattern 102 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData102 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData102 (rowMember rowData102 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData102 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_102 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData102 j b = rowTarget rowData102 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound102 : MoveSound 102 stepData102 :=
  moveSound_of_checks 102 stepData102 recoveryData102 rowData102
    transitionCode transition_checks recovery_check_102 row_check_102 move_target_102

private theorem recovery_check_103 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 103 recoveryData103 j = true := by
  have hg : seedIndices 103 = [16, 65, 139, 271, 1063] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_103 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 103 recoveryData103 rowData103 b j = true := by
  have hi : seedTransversalPattern 103 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData103 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData103 (rowMember rowData103 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData103 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_103 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData103 j b = rowTarget rowData103 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound103 : MoveSound 103 stepData103 :=
  moveSound_of_checks 103 stepData103 recoveryData103 rowData103
    transitionCode transition_checks recovery_check_103 row_check_103 move_target_103

private theorem recovery_check_104 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 104 recoveryData104 j = true := by
  have hg : seedIndices 104 = [16, 65, 139, 297, 1035] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_104 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 104 recoveryData104 rowData104 b j = true := by
  have hi : seedTransversalPattern 104 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData104 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData104 (rowMember rowData104 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData104 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_104 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData104 j b = rowTarget rowData104 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound104 : MoveSound 104 stepData104 :=
  moveSound_of_checks 104 stepData104 recoveryData104 rowData104
    transitionCode transition_checks recovery_check_104 row_check_104 move_target_104

private theorem recovery_check_105 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 105 recoveryData105 j = true := by
  have hg : seedIndices 105 = [27, 38, 137, 268] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_105 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 105 recoveryData105 rowData105 b j = true := by
  have hi : seedTransversalPattern 105 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData105 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData105 (rowMember rowData105 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData105 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_105 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData105 j b = rowTarget rowData105 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound105 : MoveSound 105 stepData105 :=
  moveSound_of_checks 105 stepData105 recoveryData105 rowData105
    transitionCode transition_checks recovery_check_105 row_check_105 move_target_105

private theorem recovery_check_106 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 106 recoveryData106 j = true := by
  have hg : seedIndices 106 = [27, 39, 139, 515, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_106 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 106 recoveryData106 rowData106 b j = true := by
  have hi : seedTransversalPattern 106 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData106 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData106 (rowMember rowData106 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData106 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_106 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData106 j b = rowTarget rowData106 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound106 : MoveSound 106 stepData106 :=
  moveSound_of_checks 106 stepData106 recoveryData106 rowData106
    transitionCode transition_checks recovery_check_106 row_check_106 move_target_106

private theorem recovery_check_107 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 107 recoveryData107 j = true := by
  have hg : seedIndices 107 = [27, 44, 128, 515, 1295] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_107 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 107 recoveryData107 rowData107 b j = true := by
  have hi : seedTransversalPattern 107 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData107 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData107 (rowMember rowData107 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData107 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_107 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData107 j b = rowTarget rowData107 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound107 : MoveSound 107 stepData107 :=
  moveSound_of_checks 107 stepData107 recoveryData107 rowData107
    transitionCode transition_checks recovery_check_107 row_check_107 move_target_107

private theorem recovery_check_108 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 108 recoveryData108 j = true := by
  have hg : seedIndices 108 = [27, 44, 128, 520, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_108 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 108 recoveryData108 rowData108 b j = true := by
  have hi : seedTransversalPattern 108 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData108 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData108 (rowMember rowData108 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData108 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_108 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData108 j b = rowTarget rowData108 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound108 : MoveSound 108 stepData108 :=
  moveSound_of_checks 108 stepData108 recoveryData108 rowData108
    transitionCode transition_checks recovery_check_108 row_check_108 move_target_108

private theorem recovery_check_109 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 109 recoveryData109 j = true := by
  have hg : seedIndices 109 = [27, 45, 137, 268] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_109 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 109 recoveryData109 rowData109 b j = true := by
  have hi : seedTransversalPattern 109 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData109 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData109 (rowMember rowData109 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData109 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_109 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData109 j b = rowTarget rowData109 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound109 : MoveSound 109 stepData109 :=
  moveSound_of_checks 109 stepData109 recoveryData109 rowData109
    transitionCode transition_checks recovery_check_109 row_check_109 move_target_109

private theorem recovery_check_110 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 110 recoveryData110 j = true := by
  have hg : seedIndices 110 = [27, 65, 128, 260, 1063] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_110 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 110 recoveryData110 rowData110 b j = true := by
  have hi : seedTransversalPattern 110 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData110 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData110 (rowMember rowData110 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData110 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_110 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData110 j b = rowTarget rowData110 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound110 : MoveSound 110 stepData110 :=
  moveSound_of_checks 110 stepData110 recoveryData110 rowData110
    transitionCode transition_checks recovery_check_110 row_check_110 move_target_110

private theorem recovery_check_111 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 111 recoveryData111 j = true := by
  have hg : seedIndices 111 = [27, 65, 128, 271, 1068] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_111 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 111 recoveryData111 rowData111 b j = true := by
  have hi : seedTransversalPattern 111 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData111 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData111 (rowMember rowData111 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData111 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_111 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData111 j b = rowTarget rowData111 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound111 : MoveSound 111 stepData111 :=
  moveSound_of_checks 111 stepData111 recoveryData111 rowData111
    transitionCode transition_checks recovery_check_111 row_check_111 move_target_111


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
