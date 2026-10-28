module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 16 through 31

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

private theorem recovery_check_016 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 16 recoveryData016 j = true := by
  have hg : seedIndices 16 = [2, 9, 16, 65, 128, 1797] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_016 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 16 recoveryData016 rowData016 b j = true := by
  have hi : seedTransversalPattern 16 = 8 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData016 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 512, 513, 516, 517, 544, 545, 548, 549, 768, 769, 772, 773, 800, 801, 804, 805] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData016 (rowMember rowData016 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 512, 513, 516, 517, 544, 545, 548, 549, 768, 769, 772, 773, 800, 801, 804, 805] (rowTarget rowData016 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_016 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData016 j b = rowTarget rowData016 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound016 : MoveSound 16 stepData016 :=
  moveSound_of_checks 16 stepData016 recoveryData016 rowData016
    transitionCode transition_checks recovery_check_016 row_check_016 move_target_016

private theorem recovery_check_017 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 17 recoveryData017 j = true := by
  have hg : seedIndices 17 = [2, 9, 16, 65, 129, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_017 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 17 recoveryData017 rowData017 b j = true := by
  have hi : seedTransversalPattern 17 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData017 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData017 (rowMember rowData017 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData017 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_017 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData017 j b = rowTarget rowData017 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound017 : MoveSound 17 stepData017 :=
  moveSound_of_checks 17 stepData017 recoveryData017 rowData017
    transitionCode transition_checks recovery_check_017 row_check_017 move_target_017

private theorem recovery_check_018 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 18 recoveryData018 j = true := by
  have hg : seedIndices 18 = [2, 9, 16, 65, 129, 517] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_018 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 18 recoveryData018 rowData018 b j = true := by
  have hi : seedTransversalPattern 18 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData018 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData018 (rowMember rowData018 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData018 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_018 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData018 j b = rowTarget rowData018 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound018 : MoveSound 18 stepData018 :=
  moveSound_of_checks 18 stepData018 recoveryData018 rowData018
    transitionCode transition_checks recovery_check_018 row_check_018 move_target_018

private theorem recovery_check_019 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 19 recoveryData019 j = true := by
  have hg : seedIndices 19 = [2, 9, 16, 65, 164, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_019 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 19 recoveryData019 rowData019 b j = true := by
  have hi : seedTransversalPattern 19 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData019 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData019 (rowMember rowData019 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData019 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_019 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData019 j b = rowTarget rowData019 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound019 : MoveSound 19 stepData019 :=
  moveSound_of_checks 19 stepData019 recoveryData019 rowData019
    transitionCode transition_checks recovery_check_019 row_check_019 move_target_019

private theorem recovery_check_020 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 20 recoveryData020 j = true := by
  have hg : seedIndices 20 = [2, 9, 16, 65, 164, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_020 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 20 recoveryData020 rowData020 b j = true := by
  have hi : seedTransversalPattern 20 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData020 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData020 (rowMember rowData020 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData020 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_020 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData020 j b = rowTarget rowData020 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound020 : MoveSound 20 stepData020 :=
  moveSound_of_checks 20 stepData020 recoveryData020 rowData020
    transitionCode transition_checks recovery_check_020 row_check_020 move_target_020

private theorem recovery_check_021 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 21 recoveryData021 j = true := by
  have hg : seedIndices 21 = [2, 9, 16, 65, 165, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_021 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 21 recoveryData021 rowData021 b j = true := by
  have hi : seedTransversalPattern 21 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData021 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData021 (rowMember rowData021 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData021 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_021 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData021 j b = rowTarget rowData021 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound021 : MoveSound 21 stepData021 :=
  moveSound_of_checks 21 stepData021 recoveryData021 rowData021
    transitionCode transition_checks recovery_check_021 row_check_021 move_target_021

private theorem recovery_check_022 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 22 recoveryData022 j = true := by
  have hg : seedIndices 22 = [2, 9, 16, 65, 165, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_022 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 22 recoveryData022 rowData022 b j = true := by
  have hi : seedTransversalPattern 22 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData022 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData022 (rowMember rowData022 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData022 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_022 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData022 j b = rowTarget rowData022 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound022 : MoveSound 22 stepData022 :=
  moveSound_of_checks 22 stepData022 recoveryData022 rowData022
    transitionCode transition_checks recovery_check_022 row_check_022 move_target_022

private theorem recovery_check_023 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 23 recoveryData023 j = true := by
  have hg : seedIndices 23 = [2, 9, 16, 65, 288] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_023 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 23 recoveryData023 rowData023 b j = true := by
  have hi : seedTransversalPattern 23 = 9 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData023 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData023 (rowMember rowData023 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] (rowTarget rowData023 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_023 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData023 j b = rowTarget rowData023 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound023 : MoveSound 23 stepData023 :=
  moveSound_of_checks 23 stepData023 recoveryData023 rowData023
    transitionCode transition_checks recovery_check_023 row_check_023 move_target_023

private theorem recovery_check_024 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 24 recoveryData024 j = true := by
  have hg : seedIndices 24 = [2, 9, 16, 65, 289] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_024 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 24 recoveryData024 rowData024 b j = true := by
  have hi : seedTransversalPattern 24 = 9 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData024 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData024 (rowMember rowData024 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] (rowTarget rowData024 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_024 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData024 j b = rowTarget rowData024 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound024 : MoveSound 24 stepData024 :=
  moveSound_of_checks 24 stepData024 recoveryData024 rowData024
    transitionCode transition_checks recovery_check_024 row_check_024 move_target_024

private theorem recovery_check_025 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 25 recoveryData025 j = true := by
  have hg : seedIndices 25 = [2, 16, 65, 128, 269] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_025 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 25 recoveryData025 rowData025 b j = true := by
  have hi : seedTransversalPattern 25 = 10 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData025 b j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 1024, 1025, 1028, 1029, 1032, 1033, 1036, 1037, 1056, 1057, 1060, 1061, 1064, 1065, 1068, 1069] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData025 (rowMember rowData025 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 1024, 1025, 1028, 1029, 1032, 1033, 1036, 1037, 1056, 1057, 1060, 1061, 1064, 1065, 1068, 1069] (rowTarget rowData025 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_025 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData025 j b = rowTarget rowData025 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound025 : MoveSound 25 stepData025 :=
  moveSound_of_checks 25 stepData025 recoveryData025 rowData025
    transitionCode transition_checks recovery_check_025 row_check_025 move_target_025

private theorem recovery_check_026 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 26 recoveryData026 j = true := by
  have hg : seedIndices 26 = [2, 16, 65, 137, 548, 1321] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_026 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 26 recoveryData026 rowData026 b j = true := by
  have hi : seedTransversalPattern 26 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData026 b j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData026 (rowMember rowData026 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData026 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_026 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData026 j b = rowTarget rowData026 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound026 : MoveSound 26 stepData026 :=
  moveSound_of_checks 26 stepData026 recoveryData026 rowData026
    transitionCode transition_checks recovery_check_026 row_check_026 move_target_026

private theorem recovery_check_027 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 27 recoveryData027 j = true := by
  have hg : seedIndices 27 = [2, 16, 65, 137, 557, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_027 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 27 recoveryData027 rowData027 b j = true := by
  have hi : seedTransversalPattern 27 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData027 b j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData027 (rowMember rowData027 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData027 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_027 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData027 j b = rowTarget rowData027 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound027 : MoveSound 27 stepData027 :=
  moveSound_of_checks 27 stepData027 recoveryData027 rowData027
    transitionCode transition_checks recovery_check_027 row_check_027 move_target_027

private theorem recovery_check_028 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 28 recoveryData028 j = true := by
  have hg : seedIndices 28 = [3, 4, 16, 64, 129] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_028 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 28 recoveryData028 rowData028 b j = true := by
  have hi : seedTransversalPattern 28 = 12 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData028 b j)
     (transitionT c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData028 (rowMember rowData028 b j)) &&
     (transitionU c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] (rowTarget rowData028 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_028 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData028 j b = rowTarget rowData028 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound028 : MoveSound 28 stepData028 :=
  moveSound_of_checks 28 stepData028 recoveryData028 rowData028
    transitionCode transition_checks recovery_check_028 row_check_028 move_target_028

private theorem recovery_check_029 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 29 recoveryData029 j = true := by
  have hg : seedIndices 29 = [3, 4, 16, 65, 128] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_029 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 29 recoveryData029 rowData029 b j = true := by
  have hi : seedTransversalPattern 29 = 12 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData029 b j)
     (transitionT c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData029 (rowMember rowData029 b j)) &&
     (transitionU c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] (rowTarget rowData029 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_029 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData029 j b = rowTarget rowData029 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound029 : MoveSound 29 stepData029 :=
  moveSound_of_checks 29 stepData029 recoveryData029 rowData029
    transitionCode transition_checks recovery_check_029 row_check_029 move_target_029

private theorem recovery_check_030 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 30 recoveryData030 j = true := by
  have hg : seedIndices 30 = [3, 8, 16, 65, 128, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_030 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 30 recoveryData030 rowData030 b j = true := by
  have hi : seedTransversalPattern 30 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData030 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData030 (rowMember rowData030 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData030 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_030 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData030 j b = rowTarget rowData030 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound030 : MoveSound 30 stepData030 :=
  moveSound_of_checks 30 stepData030 recoveryData030 rowData030
    transitionCode transition_checks recovery_check_030 row_check_030 move_target_030

private theorem recovery_check_031 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 31 recoveryData031 j = true := by
  have hg : seedIndices 31 = [3, 8, 16, 65, 128, 545] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_031 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 31 recoveryData031 rowData031 b j = true := by
  have hi : seedTransversalPattern 31 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData031 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData031 (rowMember rowData031 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData031 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_031 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData031 j b = rowTarget rowData031 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound031 : MoveSound 31 stepData031 :=
  moveSound_of_checks 31 stepData031 recoveryData031 rowData031
    transitionCode transition_checks recovery_check_031 row_check_031 move_target_031


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
