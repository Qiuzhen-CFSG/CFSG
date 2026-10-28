module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 48 through 63

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

private theorem recovery_check_048 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 48 recoveryData048 j = true := by
  have hg : seedIndices 48 = [11, 16, 36, 128, 515] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_048 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 48 recoveryData048 rowData048 b j = true := by
  have hi : seedTransversalPattern 48 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData048 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData048 (rowMember rowData048 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData048 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_048 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData048 j b = rowTarget rowData048 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound048 : MoveSound 48 stepData048 :=
  moveSound_of_checks 48 stepData048 recoveryData048 rowData048
    transitionCode transition_checks recovery_check_048 row_check_048 move_target_048

private theorem recovery_check_049 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 49 recoveryData049 j = true := by
  have hg : seedIndices 49 = [11, 16, 36, 129, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_049 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 49 recoveryData049 rowData049 b j = true := by
  have hi : seedTransversalPattern 49 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData049 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData049 (rowMember rowData049 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData049 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_049 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData049 j b = rowTarget rowData049 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound049 : MoveSound 49 stepData049 :=
  moveSound_of_checks 49 stepData049 recoveryData049 rowData049
    transitionCode transition_checks recovery_check_049 row_check_049 move_target_049

private theorem recovery_check_050 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 50 recoveryData050 j = true := by
  have hg : seedIndices 50 = [11, 16, 36, 129, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_050 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 50 recoveryData050 rowData050 b j = true := by
  have hi : seedTransversalPattern 50 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData050 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData050 (rowMember rowData050 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData050 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_050 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData050 j b = rowTarget rowData050 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound050 : MoveSound 50 stepData050 :=
  moveSound_of_checks 50 stepData050 recoveryData050 rowData050
    transitionCode transition_checks recovery_check_050 row_check_050 move_target_050

private theorem recovery_check_051 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 51 recoveryData051 j = true := by
  have hg : seedIndices 51 = [11, 16, 36, 129, 515] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_051 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 51 recoveryData051 rowData051 b j = true := by
  have hi : seedTransversalPattern 51 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData051 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData051 (rowMember rowData051 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData051 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_051 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData051 j b = rowTarget rowData051 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound051 : MoveSound 51 stepData051 :=
  moveSound_of_checks 51 stepData051 recoveryData051 rowData051
    transitionCode transition_checks recovery_check_051 row_check_051 move_target_051

private theorem recovery_check_052 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 52 recoveryData052 j = true := by
  have hg : seedIndices 52 = [11, 16, 37, 128, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_052 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 52 recoveryData052 rowData052 b j = true := by
  have hi : seedTransversalPattern 52 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData052 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData052 (rowMember rowData052 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData052 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_052 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData052 j b = rowTarget rowData052 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound052 : MoveSound 52 stepData052 :=
  moveSound_of_checks 52 stepData052 recoveryData052 rowData052
    transitionCode transition_checks recovery_check_052 row_check_052 move_target_052

private theorem recovery_check_053 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 53 recoveryData053 j = true := by
  have hg : seedIndices 53 = [11, 16, 37, 128, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_053 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 53 recoveryData053 rowData053 b j = true := by
  have hi : seedTransversalPattern 53 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData053 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData053 (rowMember rowData053 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData053 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_053 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData053 j b = rowTarget rowData053 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound053 : MoveSound 53 stepData053 :=
  moveSound_of_checks 53 stepData053 recoveryData053 rowData053
    transitionCode transition_checks recovery_check_053 row_check_053 move_target_053

private theorem recovery_check_054 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 54 recoveryData054 j = true := by
  have hg : seedIndices 54 = [11, 16, 37, 128, 515] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_054 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 54 recoveryData054 rowData054 b j = true := by
  have hi : seedTransversalPattern 54 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData054 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData054 (rowMember rowData054 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData054 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_054 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData054 j b = rowTarget rowData054 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound054 : MoveSound 54 stepData054 :=
  moveSound_of_checks 54 stepData054 recoveryData054 rowData054
    transitionCode transition_checks recovery_check_054 row_check_054 move_target_054

private theorem recovery_check_055 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 55 recoveryData055 j = true := by
  have hg : seedIndices 55 = [11, 16, 37, 128, 1797] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_055 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 55 recoveryData055 rowData055 b j = true := by
  have hi : seedTransversalPattern 55 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData055 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData055 (rowMember rowData055 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData055 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_055 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData055 j b = rowTarget rowData055 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound055 : MoveSound 55 stepData055 :=
  moveSound_of_checks 55 stepData055 recoveryData055 rowData055
    transitionCode transition_checks recovery_check_055 row_check_055 move_target_055

private theorem recovery_check_056 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 56 recoveryData056 j = true := by
  have hg : seedIndices 56 = [11, 16, 38, 130, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_056 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 56 recoveryData056 rowData056 b j = true := by
  have hi : seedTransversalPattern 56 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData056 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData056 (rowMember rowData056 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData056 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_056 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData056 j b = rowTarget rowData056 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound056 : MoveSound 56 stepData056 :=
  moveSound_of_checks 56 stepData056 recoveryData056 rowData056
    transitionCode transition_checks recovery_check_056 row_check_056 move_target_056

private theorem recovery_check_057 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 57 recoveryData057 j = true := by
  have hg : seedIndices 57 = [11, 16, 38, 130, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_057 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 57 recoveryData057 rowData057 b j = true := by
  have hi : seedTransversalPattern 57 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData057 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData057 (rowMember rowData057 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData057 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_057 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData057 j b = rowTarget rowData057 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound057 : MoveSound 57 stepData057 :=
  moveSound_of_checks 57 stepData057 recoveryData057 rowData057
    transitionCode transition_checks recovery_check_057 row_check_057 move_target_057

private theorem recovery_check_058 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 58 recoveryData058 j = true := by
  have hg : seedIndices 58 = [11, 16, 38, 131, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_058 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 58 recoveryData058 rowData058 b j = true := by
  have hi : seedTransversalPattern 58 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData058 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData058 (rowMember rowData058 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData058 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_058 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData058 j b = rowTarget rowData058 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound058 : MoveSound 58 stepData058 :=
  moveSound_of_checks 58 stepData058 recoveryData058 rowData058
    transitionCode transition_checks recovery_check_058 row_check_058 move_target_058

private theorem recovery_check_059 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 59 recoveryData059 j = true := by
  have hg : seedIndices 59 = [11, 16, 39, 128, 1797] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_059 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 59 recoveryData059 rowData059 b j = true := by
  have hi : seedTransversalPattern 59 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData059 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData059 (rowMember rowData059 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData059 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_059 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData059 j b = rowTarget rowData059 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound059 : MoveSound 59 stepData059 :=
  moveSound_of_checks 59 stepData059 recoveryData059 rowData059
    transitionCode transition_checks recovery_check_059 row_check_059 move_target_059

private theorem recovery_check_060 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 60 recoveryData060 j = true := by
  have hg : seedIndices 60 = [11, 16, 39, 128, 1799] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_060 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 60 recoveryData060 rowData060 b j = true := by
  have hi : seedTransversalPattern 60 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData060 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData060 (rowMember rowData060 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData060 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_060 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData060 j b = rowTarget rowData060 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound060 : MoveSound 60 stepData060 :=
  moveSound_of_checks 60 stepData060 recoveryData060 rowData060
    transitionCode transition_checks recovery_check_060 row_check_060 move_target_060

private theorem recovery_check_061 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 61 recoveryData061 j = true := by
  have hg : seedIndices 61 = [11, 16, 39, 130, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_061 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 61 recoveryData061 rowData061 b j = true := by
  have hi : seedTransversalPattern 61 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData061 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData061 (rowMember rowData061 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData061 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_061 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData061 j b = rowTarget rowData061 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound061 : MoveSound 61 stepData061 :=
  moveSound_of_checks 61 stepData061 recoveryData061 rowData061
    transitionCode transition_checks recovery_check_061 row_check_061 move_target_061

private theorem recovery_check_062 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 62 recoveryData062 j = true := by
  have hg : seedIndices 62 = [11, 16, 65, 128, 261] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_062 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 62 recoveryData062 rowData062 b j = true := by
  have hi : seedTransversalPattern 62 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData062 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData062 (rowMember rowData062 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData062 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_062 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData062 j b = rowTarget rowData062 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound062 : MoveSound 62 stepData062 :=
  moveSound_of_checks 62 stepData062 recoveryData062 rowData062
    transitionCode transition_checks recovery_check_062 row_check_062 move_target_062

private theorem recovery_check_063 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 63 recoveryData063 j = true := by
  have hg : seedIndices 63 = [11, 16, 65, 128, 290] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_063 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 63 recoveryData063 rowData063 b j = true := by
  have hi : seedTransversalPattern 63 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData063 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData063 (rowMember rowData063 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData063 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_063 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData063 j b = rowTarget rowData063 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound063 : MoveSound 63 stepData063 :=
  moveSound_of_checks 63 stepData063 recoveryData063 rowData063
    transitionCode transition_checks recovery_check_063 row_check_063 move_target_063


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
