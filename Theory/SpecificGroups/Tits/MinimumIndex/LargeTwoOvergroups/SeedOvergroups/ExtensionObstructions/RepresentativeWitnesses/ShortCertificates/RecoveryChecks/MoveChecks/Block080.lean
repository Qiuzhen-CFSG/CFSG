module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 80 through 95

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

private theorem recovery_check_080 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 80 recoveryData080 j = true := by
  have hg : seedIndices 80 = [11, 16, 65, 167, 548, 1284] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_080 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 80 recoveryData080 rowData080 b j = true := by
  have hi : seedTransversalPattern 80 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData080 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData080 (rowMember rowData080 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData080 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_080 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData080 j b = rowTarget rowData080 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound080 : MoveSound 80 stepData080 :=
  moveSound_of_checks 80 stepData080 recoveryData080 rowData080
    transitionCode transition_checks recovery_check_080 row_check_080 move_target_080

private theorem recovery_check_081 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 81 recoveryData081 j = true := by
  have hg : seedIndices 81 = [11, 16, 65, 167, 548, 1285] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_081 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 81 recoveryData081 rowData081 b j = true := by
  have hi : seedTransversalPattern 81 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData081 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData081 (rowMember rowData081 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData081 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_081 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData081 j b = rowTarget rowData081 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound081 : MoveSound 81 stepData081 :=
  moveSound_of_checks 81 stepData081 recoveryData081 rowData081
    transitionCode transition_checks recovery_check_081 row_check_081 move_target_081

private theorem recovery_check_082 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 82 recoveryData082 j = true := by
  have hg : seedIndices 82 = [11, 16, 65, 288, 1061] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_082 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 82 recoveryData082 rowData082 b j = true := by
  have hi : seedTransversalPattern 82 = 18 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData082 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData082 (rowMember rowData082 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] (rowTarget rowData082 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_082 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData082 j b = rowTarget rowData082 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound082 : MoveSound 82 stepData082 :=
  moveSound_of_checks 82 stepData082 recoveryData082 rowData082
    transitionCode transition_checks recovery_check_082 row_check_082 move_target_082

private theorem recovery_check_083 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 83 recoveryData083 j = true := by
  have hg : seedIndices 83 = [11, 16, 65, 291, 1057] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_083 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 83 recoveryData083 rowData083 b j = true := by
  have hi : seedTransversalPattern 83 = 18 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData083 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData083 (rowMember rowData083 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] (rowTarget rowData083 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_083 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData083 j b = rowTarget rowData083 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound083 : MoveSound 83 stepData083 :=
  moveSound_of_checks 83 stepData083 recoveryData083 rowData083
    transitionCode transition_checks recovery_check_083 row_check_083 move_target_083

private theorem recovery_check_084 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 84 recoveryData084 j = true := by
  have hg : seedIndices 84 = [11, 17, 32, 129, 518] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_084 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 84 recoveryData084 rowData084 b j = true := by
  have hi : seedTransversalPattern 84 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData084 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData084 (rowMember rowData084 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData084 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_084 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData084 j b = rowTarget rowData084 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound084 : MoveSound 84 stepData084 :=
  moveSound_of_checks 84 stepData084 recoveryData084 rowData084
    transitionCode transition_checks recovery_check_084 row_check_084 move_target_084

private theorem recovery_check_085 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 85 recoveryData085 j = true := by
  have hg : seedIndices 85 = [11, 17, 33, 129, 518] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_085 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 85 recoveryData085 rowData085 b j = true := by
  have hi : seedTransversalPattern 85 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData085 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData085 (rowMember rowData085 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData085 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_085 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData085 j b = rowTarget rowData085 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound085 : MoveSound 85 stepData085 :=
  moveSound_of_checks 85 stepData085 recoveryData085 rowData085
    transitionCode transition_checks recovery_check_085 row_check_085 move_target_085

private theorem recovery_check_086 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 86 recoveryData086 j = true := by
  have hg : seedIndices 86 = [11, 17, 34, 130, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_086 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 86 recoveryData086 rowData086 b j = true := by
  have hi : seedTransversalPattern 86 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData086 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData086 (rowMember rowData086 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData086 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_086 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData086 j b = rowTarget rowData086 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound086 : MoveSound 86 stepData086 :=
  moveSound_of_checks 86 stepData086 recoveryData086 rowData086
    transitionCode transition_checks recovery_check_086 row_check_086 move_target_086

private theorem recovery_check_087 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 87 recoveryData087 j = true := by
  have hg : seedIndices 87 = [11, 17, 35, 130, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_087 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 87 recoveryData087 rowData087 b j = true := by
  have hi : seedTransversalPattern 87 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData087 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData087 (rowMember rowData087 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData087 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_087 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData087 j b = rowTarget rowData087 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound087 : MoveSound 87 stepData087 :=
  moveSound_of_checks 87 stepData087 recoveryData087 rowData087
    transitionCode transition_checks recovery_check_087 row_check_087 move_target_087

private theorem recovery_check_088 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 88 recoveryData088 j = true := by
  have hg : seedIndices 88 = [11, 18, 65, 128, 548, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_088 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 88 recoveryData088 rowData088 b j = true := by
  have hi : seedTransversalPattern 88 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData088 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData088 (rowMember rowData088 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData088 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_088 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData088 j b = rowTarget rowData088 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound088 : MoveSound 88 stepData088 :=
  moveSound_of_checks 88 stepData088 recoveryData088 rowData088
    transitionCode transition_checks recovery_check_088 row_check_088 move_target_088

private theorem recovery_check_089 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 89 recoveryData089 j = true := by
  have hg : seedIndices 89 = [11, 18, 65, 128, 550, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_089 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 89 recoveryData089 rowData089 b j = true := by
  have hi : seedTransversalPattern 89 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData089 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData089 (rowMember rowData089 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData089 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_089 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData089 j b = rowTarget rowData089 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound089 : MoveSound 89 stepData089 :=
  moveSound_of_checks 89 stepData089 recoveryData089 rowData089
    transitionCode transition_checks recovery_check_089 row_check_089 move_target_089

private theorem recovery_check_090 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 90 recoveryData090 j = true := by
  have hg : seedIndices 90 = [11, 65, 128, 290, 1040] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_090 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 90 recoveryData090 rowData090 b j = true := by
  have hi : seedTransversalPattern 90 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData090 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData090 (rowMember rowData090 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData090 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_090 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData090 j b = rowTarget rowData090 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound090 : MoveSound 90 stepData090 :=
  moveSound_of_checks 90 stepData090 recoveryData090 rowData090
    transitionCode transition_checks recovery_check_090 row_check_090 move_target_090

private theorem recovery_check_091 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 91 recoveryData091 j = true := by
  have hg : seedIndices 91 = [11, 65, 144, 260, 1079] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_091 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 91 recoveryData091 rowData091 b j = true := by
  have hi : seedTransversalPattern 91 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData091 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData091 (rowMember rowData091 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData091 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_091 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData091 j b = rowTarget rowData091 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound091 : MoveSound 91 stepData091 :=
  moveSound_of_checks 91 stepData091 recoveryData091 rowData091
    transitionCode transition_checks recovery_check_091 row_check_091 move_target_091

private theorem recovery_check_092 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 92 recoveryData092 j = true := by
  have hg : seedIndices 92 = [11, 65, 144, 288, 1042] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_092 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 92 recoveryData092 rowData092 b j = true := by
  have hi : seedTransversalPattern 92 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData092 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData092 (rowMember rowData092 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData092 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_092 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData092 j b = rowTarget rowData092 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound092 : MoveSound 92 stepData092 :=
  moveSound_of_checks 92 stepData092 recoveryData092 rowData092
    transitionCode transition_checks recovery_check_092 row_check_092 move_target_092

private theorem recovery_check_093 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 93 recoveryData093 j = true := by
  have hg : seedIndices 93 = [11, 65, 144, 306, 1024] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_093 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 93 recoveryData093 rowData093 b j = true := by
  have hi : seedTransversalPattern 93 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData093 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData093 (rowMember rowData093 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData093 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_093 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData093 j b = rowTarget rowData093 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound093 : MoveSound 93 stepData093 :=
  moveSound_of_checks 93 stepData093 recoveryData093 rowData093
    transitionCode transition_checks recovery_check_093 row_check_093 move_target_093

private theorem recovery_check_094 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 94 recoveryData094 j = true := by
  have hg : seedIndices 94 = [16, 37, 128, 513, 1293] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_094 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 94 recoveryData094 rowData094 b j = true := by
  have hi : seedTransversalPattern 94 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData094 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData094 (rowMember rowData094 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData094 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_094 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData094 j b = rowTarget rowData094 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound094 : MoveSound 94 stepData094 :=
  moveSound_of_checks 94 stepData094 recoveryData094 rowData094
    transitionCode transition_checks recovery_check_094 row_check_094 move_target_094

private theorem recovery_check_095 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 95 recoveryData095 j = true := by
  have hg : seedIndices 95 = [16, 37, 128, 522, 1286] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_095 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 95 recoveryData095 rowData095 b j = true := by
  have hi : seedTransversalPattern 95 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData095 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData095 (rowMember rowData095 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData095 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_095 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData095 j b = rowTarget rowData095 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound095 : MoveSound 95 stepData095 :=
  moveSound_of_checks 95 stepData095 recoveryData095 rowData095
    transitionCode transition_checks recovery_check_095 row_check_095 move_target_095


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
