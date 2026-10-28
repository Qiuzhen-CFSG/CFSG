module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 32 through 47

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

private theorem recovery_check_032 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 32 recoveryData032 j = true := by
  have hg : seedIndices 32 = [3, 8, 16, 65, 165, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_032 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 32 recoveryData032 rowData032 b j = true := by
  have hi : seedTransversalPattern 32 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData032 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData032 (rowMember rowData032 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData032 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_032 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData032 j b = rowTarget rowData032 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound032 : MoveSound 32 stepData032 :=
  moveSound_of_checks 32 stepData032 recoveryData032 rowData032
    transitionCode transition_checks recovery_check_032 row_check_032 move_target_032

private theorem recovery_check_033 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 33 recoveryData033 j = true := by
  have hg : seedIndices 33 = [3, 8, 16, 65, 165, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_033 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 33 recoveryData033 rowData033 b j = true := by
  have hi : seedTransversalPattern 33 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData033 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData033 (rowMember rowData033 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData033 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_033 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData033 j b = rowTarget rowData033 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound033 : MoveSound 33 stepData033 :=
  moveSound_of_checks 33 stepData033 recoveryData033 rowData033
    transitionCode transition_checks recovery_check_033 row_check_033 move_target_033

private theorem recovery_check_034 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 34 recoveryData034 j = true := by
  have hg : seedIndices 34 = [3, 8, 16, 65, 165, 548] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_034 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 34 recoveryData034 rowData034 b j = true := by
  have hi : seedTransversalPattern 34 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData034 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData034 (rowMember rowData034 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData034 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_034 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData034 j b = rowTarget rowData034 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound034 : MoveSound 34 stepData034 :=
  moveSound_of_checks 34 stepData034 recoveryData034 rowData034
    transitionCode transition_checks recovery_check_034 row_check_034 move_target_034

private theorem recovery_check_035 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 35 recoveryData035 j = true := by
  have hg : seedIndices 35 = [3, 8, 16, 65, 512, 1313] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_035 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 35 recoveryData035 rowData035 b j = true := by
  have hi : seedTransversalPattern 35 = 13 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData035 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData035 (rowMember rowData035 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] (rowTarget rowData035 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_035 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData035 j b = rowTarget rowData035 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound035 : MoveSound 35 stepData035 :=
  moveSound_of_checks 35 stepData035 recoveryData035 rowData035
    transitionCode transition_checks recovery_check_035 row_check_035 move_target_035

private theorem recovery_check_036 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 36 recoveryData036 j = true := by
  have hg : seedIndices 36 = [3, 8, 16, 65, 512, 1412] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_036 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 36 recoveryData036 rowData036 b j = true := by
  have hi : seedTransversalPattern 36 = 13 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData036 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData036 (rowMember rowData036 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] (rowTarget rowData036 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_036 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData036 j b = rowTarget rowData036 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound036 : MoveSound 36 stepData036 :=
  moveSound_of_checks 36 stepData036 recoveryData036 rowData036
    transitionCode transition_checks recovery_check_036 row_check_036 move_target_036

private theorem recovery_check_037 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 37 recoveryData037 j = true := by
  have hg : seedIndices 37 = [3, 24, 65, 164, 520, 1313] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_037 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 37 recoveryData037 rowData037 b j = true := by
  have hi : seedTransversalPattern 37 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData037 b j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData037 (rowMember rowData037 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData037 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_037 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData037 j b = rowTarget rowData037 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound037 : MoveSound 37 stepData037 :=
  moveSound_of_checks 37 stepData037 recoveryData037 rowData037
    transitionCode transition_checks recovery_check_037 row_check_037 move_target_037

private theorem recovery_check_038 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 38 recoveryData038 j = true := by
  have hg : seedIndices 38 = [3, 24, 65, 164, 520, 1321] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_038 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 38 recoveryData038 rowData038 b j = true := by
  have hi : seedTransversalPattern 38 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData038 b j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData038 (rowMember rowData038 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData038 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_038 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData038 j b = rowTarget rowData038 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound038 : MoveSound 38 stepData038 :=
  moveSound_of_checks 38 stepData038 recoveryData038 rowData038
    transitionCode transition_checks recovery_check_038 row_check_038 move_target_038

private theorem recovery_check_039 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 39 recoveryData039 j = true := by
  have hg : seedIndices 39 = [8, 19, 65, 164, 512, 1313] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_039 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 39 recoveryData039 rowData039 b j = true := by
  have hi : seedTransversalPattern 39 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData039 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData039 (rowMember rowData039 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData039 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_039 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData039 j b = rowTarget rowData039 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound039 : MoveSound 39 stepData039 :=
  moveSound_of_checks 39 stepData039 recoveryData039 rowData039
    transitionCode transition_checks recovery_check_039 row_check_039 move_target_039

private theorem recovery_check_040 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 40 recoveryData040 j = true := by
  have hg : seedIndices 40 = [8, 19, 65, 164, 512, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_040 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 40 recoveryData040 rowData040 b j = true := by
  have hi : seedTransversalPattern 40 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData040 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData040 (rowMember rowData040 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData040 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_040 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData040 j b = rowTarget rowData040 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound040 : MoveSound 40 stepData040 :=
  moveSound_of_checks 40 stepData040 recoveryData040 rowData040
    transitionCode transition_checks recovery_check_040 row_check_040 move_target_040

private theorem recovery_check_041 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 41 recoveryData041 j = true := by
  have hg : seedIndices 41 = [9, 16, 65, 130, 262] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_041 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 41 recoveryData041 rowData041 b j = true := by
  have hi : seedTransversalPattern 41 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData041 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData041 (rowMember rowData041 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData041 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_041 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData041 j b = rowTarget rowData041 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound041 : MoveSound 41 stepData041 :=
  moveSound_of_checks 41 stepData041 recoveryData041 rowData041
    transitionCode transition_checks recovery_check_041 row_check_041 move_target_041

private theorem recovery_check_042 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 42 recoveryData042 j = true := by
  have hg : seedIndices 42 = [9, 16, 65, 130, 548, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_042 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 42 recoveryData042 rowData042 b j = true := by
  have hi : seedTransversalPattern 42 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData042 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData042 (rowMember rowData042 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData042 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_042 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData042 j b = rowTarget rowData042 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound042 : MoveSound 42 stepData042 :=
  moveSound_of_checks 42 stepData042 recoveryData042 rowData042
    transitionCode transition_checks recovery_check_042 row_check_042 move_target_042

private theorem recovery_check_043 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 43 recoveryData043 j = true := by
  have hg : seedIndices 43 = [9, 18, 65, 130, 548, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_043 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 43 recoveryData043 rowData043 b j = true := by
  have hi : seedTransversalPattern 43 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData043 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData043 (rowMember rowData043 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData043 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_043 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData043 j b = rowTarget rowData043 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound043 : MoveSound 43 stepData043 :=
  moveSound_of_checks 43 stepData043 recoveryData043 rowData043
    transitionCode transition_checks recovery_check_043 row_check_043 move_target_043

private theorem recovery_check_044 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 44 recoveryData044 j = true := by
  have hg : seedIndices 44 = [9, 18, 65, 130, 550, 1312] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_044 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 44 recoveryData044 rowData044 b j = true := by
  have hi : seedTransversalPattern 44 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData044 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData044 (rowMember rowData044 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData044 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_044 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData044 j b = rowTarget rowData044 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound044 : MoveSound 44 stepData044 :=
  moveSound_of_checks 44 stepData044 recoveryData044 rowData044
    transitionCode transition_checks recovery_check_044 row_check_044 move_target_044

private theorem recovery_check_045 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 45 recoveryData045 j = true := by
  have hg : seedIndices 45 = [9, 18, 65, 130, 550, 1314] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_045 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 45 recoveryData045 rowData045 b j = true := by
  have hi : seedTransversalPattern 45 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData045 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData045 (rowMember rowData045 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData045 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_045 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData045 j b = rowTarget rowData045 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound045 : MoveSound 45 stepData045 :=
  moveSound_of_checks 45 stepData045 recoveryData045 rowData045
    transitionCode transition_checks recovery_check_045 row_check_045 move_target_045

private theorem recovery_check_046 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 46 recoveryData046 j = true := by
  have hg : seedIndices 46 = [11, 16, 36, 128, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_046 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 46 recoveryData046 rowData046 b j = true := by
  have hi : seedTransversalPattern 46 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData046 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData046 (rowMember rowData046 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData046 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_046 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData046 j b = rowTarget rowData046 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound046 : MoveSound 46 stepData046 :=
  moveSound_of_checks 46 stepData046 recoveryData046 rowData046
    transitionCode transition_checks recovery_check_046 row_check_046 move_target_046

private theorem recovery_check_047 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 47 recoveryData047 j = true := by
  have hg : seedIndices 47 = [11, 16, 36, 128, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_047 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 47 recoveryData047 rowData047 b j = true := by
  have hi : seedTransversalPattern 47 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData047 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData047 (rowMember rowData047 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData047 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_047 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData047 j b = rowTarget rowData047 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound047 : MoveSound 47 stepData047 :=
  moveSound_of_checks 47 stepData047 recoveryData047 rowData047
    transitionCode transition_checks recovery_check_047 row_check_047 move_target_047


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
