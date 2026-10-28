module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 0 through 15

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

private theorem recovery_check_000 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 0 recoveryData000 j = true := by
  have hg : seedIndices 0 = [1, 2, 4, 16, 64] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_000 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 0 recoveryData000 rowData000 b j = true := by
  have hi : seedTransversalPattern 0 = 0 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData000 b j)
     (transitionT c == ![0, 32, 128, 160, 256, 288, 384, 416, 512, 544, 640, 672, 768, 800, 896, 928, 1024, 1056, 1152, 1184, 1280, 1312, 1408, 1440, 1536, 1568, 1664, 1696, 1792, 1824, 1920, 1952] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData000 (rowMember rowData000 b j)) &&
     (transitionU c == ![0, 32, 128, 160, 256, 288, 384, 416, 512, 544, 640, 672, 768, 800, 896, 928, 1024, 1056, 1152, 1184, 1280, 1312, 1408, 1440, 1536, 1568, 1664, 1696, 1792, 1824, 1920, 1952] (rowTarget rowData000 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_000 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData000 j b = rowTarget rowData000 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound000 : MoveSound 0 stepData000 :=
  moveSound_of_checks 0 stepData000 recoveryData000 rowData000
    transitionCode transition_checks recovery_check_000 row_check_000 move_target_000

private theorem recovery_check_001 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 1 recoveryData001 j = true := by
  have hg : seedIndices 1 = [1, 2, 4, 16, 160] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_001 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 1 recoveryData001 rowData001 b j = true := by
  have hi : seedTransversalPattern 1 = 1 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData001 b j)
     (transitionT c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData001 (rowMember rowData001 b j)) &&
     (transitionU c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] (rowTarget rowData001 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_001 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData001 j b = rowTarget rowData001 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound001 : MoveSound 1 stepData001 :=
  moveSound_of_checks 1 stepData001 recoveryData001 rowData001
    transitionCode transition_checks recovery_check_001 row_check_001 move_target_001

private theorem recovery_check_002 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 2 recoveryData002 j = true := by
  have hg : seedIndices 2 = [1, 2, 4, 16, 192] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_002 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 2 recoveryData002 rowData002 b j = true := by
  have hi : seedTransversalPattern 2 = 1 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData002 b j)
     (transitionT c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData002 (rowMember rowData002 b j)) &&
     (transitionU c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] (rowTarget rowData002 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_002 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData002 j b = rowTarget rowData002 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound002 : MoveSound 2 stepData002 :=
  moveSound_of_checks 2 stepData002 recoveryData002 rowData002
    transitionCode transition_checks recovery_check_002 row_check_002 move_target_002

private theorem recovery_check_003 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 3 recoveryData003 j = true := by
  have hg : seedIndices 3 = [1, 2, 8, 16, 64, 164] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_003 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 3 recoveryData003 rowData003 b j = true := by
  have hi : seedTransversalPattern 3 = 2 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData003 b j)
     (transitionT c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData003 (rowMember rowData003 b j)) &&
     (transitionU c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] (rowTarget rowData003 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_003 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData003 j b = rowTarget rowData003 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound003 : MoveSound 3 stepData003 :=
  moveSound_of_checks 3 stepData003 recoveryData003 rowData003
    transitionCode transition_checks recovery_check_003 row_check_003 move_target_003

private theorem recovery_check_004 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 4 recoveryData004 j = true := by
  have hg : seedIndices 4 = [1, 2, 8, 16, 64, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_004 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 4 recoveryData004 rowData004 b j = true := by
  have hi : seedTransversalPattern 4 = 3 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData004 b j)
     (transitionT c == ![0, 4, 32, 36, 128, 132, 160, 164, 256, 260, 288, 292, 384, 388, 416, 420, 1024, 1028, 1056, 1060, 1152, 1156, 1184, 1188, 1280, 1284, 1312, 1316, 1408, 1412, 1440, 1444] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData004 (rowMember rowData004 b j)) &&
     (transitionU c == ![0, 4, 32, 36, 128, 132, 160, 164, 256, 260, 288, 292, 384, 388, 416, 420, 1024, 1028, 1056, 1060, 1152, 1156, 1184, 1188, 1280, 1284, 1312, 1316, 1408, 1412, 1440, 1444] (rowTarget rowData004 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_004 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData004 j b = rowTarget rowData004 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound004 : MoveSound 4 stepData004 :=
  moveSound_of_checks 4 stepData004 recoveryData004 rowData004
    transitionCode transition_checks recovery_check_004 row_check_004 move_target_004

private theorem recovery_check_005 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 5 recoveryData005 j = true := by
  have hg : seedIndices 5 = [1, 2, 8, 16, 68, 164] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_005 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 5 recoveryData005 rowData005 b j = true := by
  have hi : seedTransversalPattern 5 = 2 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData005 b j)
     (transitionT c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData005 (rowMember rowData005 b j)) &&
     (transitionU c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] (rowTarget rowData005 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_005 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData005 j b = rowTarget rowData005 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound005 : MoveSound 5 stepData005 :=
  moveSound_of_checks 5 stepData005 recoveryData005 rowData005
    transitionCode transition_checks recovery_check_005 row_check_005 move_target_005

private theorem recovery_check_006 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 6 recoveryData006 j = true := by
  have hg : seedIndices 6 = [1, 10, 16, 34, 130] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_006 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 6 recoveryData006 rowData006 b j = true := by
  have hi : seedTransversalPattern 6 = 4 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData006 b j)
     (transitionT c == ![0, 2, 4, 6, 256, 258, 260, 262, 512, 514, 516, 518, 768, 770, 772, 774, 1024, 1026, 1028, 1030, 1280, 1282, 1284, 1286, 1536, 1538, 1540, 1542, 1792, 1794, 1796, 1798] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData006 (rowMember rowData006 b j)) &&
     (transitionU c == ![0, 2, 4, 6, 256, 258, 260, 262, 512, 514, 516, 518, 768, 770, 772, 774, 1024, 1026, 1028, 1030, 1280, 1282, 1284, 1286, 1536, 1538, 1540, 1542, 1792, 1794, 1796, 1798] (rowTarget rowData006 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_006 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData006 j b = rowTarget rowData006 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound006 : MoveSound 6 stepData006 :=
  moveSound_of_checks 6 stepData006 recoveryData006 rowData006
    transitionCode transition_checks recovery_check_006 row_check_006 move_target_006

private theorem recovery_check_007 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 7 recoveryData007 j = true := by
  have hg : seedIndices 7 = [1, 10, 16, 64, 130, 546] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_007 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 7 recoveryData007 rowData007 b j = true := by
  have hi : seedTransversalPattern 7 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData007 b j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData007 (rowMember rowData007 b j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData007 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_007 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData007 j b = rowTarget rowData007 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound007 : MoveSound 7 stepData007 :=
  moveSound_of_checks 7 stepData007 recoveryData007 rowData007
    transitionCode transition_checks recovery_check_007 row_check_007 move_target_007

private theorem recovery_check_008 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 8 recoveryData008 j = true := by
  have hg : seedIndices 8 = [1, 10, 16, 64, 164, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_008 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 8 recoveryData008 rowData008 b j = true := by
  have hi : seedTransversalPattern 8 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData008 b j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData008 (rowMember rowData008 b j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData008 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_008 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData008 j b = rowTarget rowData008 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound008 : MoveSound 8 stepData008 :=
  moveSound_of_checks 8 stepData008 recoveryData008 rowData008
    transitionCode transition_checks recovery_check_008 row_check_008 move_target_008

private theorem recovery_check_009 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 9 recoveryData009 j = true := by
  have hg : seedIndices 9 = [1, 10, 16, 64, 164, 514] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_009 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 9 recoveryData009 rowData009 b j = true := by
  have hi : seedTransversalPattern 9 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData009 b j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData009 (rowMember rowData009 b j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData009 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_009 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData009 j b = rowTarget rowData009 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound009 : MoveSound 9 stepData009 :=
  moveSound_of_checks 9 stepData009 recoveryData009 rowData009
    transitionCode transition_checks recovery_check_009 row_check_009 move_target_009

private theorem recovery_check_010 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 10 recoveryData010 j = true := by
  have hg : seedIndices 10 = [1, 10, 16, 64, 164, 548] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_010 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 10 recoveryData010 rowData010 b j = true := by
  have hi : seedTransversalPattern 10 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData010 b j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData010 (rowMember rowData010 b j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData010 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_010 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData010 j b = rowTarget rowData010 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound010 : MoveSound 10 stepData010 :=
  moveSound_of_checks 10 stepData010 recoveryData010 rowData010
    transitionCode transition_checks recovery_check_010 row_check_010 move_target_010

private theorem recovery_check_011 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 11 recoveryData011 j = true := by
  have hg : seedIndices 11 = [2, 9, 16, 36, 128] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_011 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 11 recoveryData011 rowData011 b j = true := by
  have hi : seedTransversalPattern 11 = 6 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData011 b j)
     (transitionT c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData011 (rowMember rowData011 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] (rowTarget rowData011 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_011 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData011 j b = rowTarget rowData011 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound011 : MoveSound 11 stepData011 :=
  moveSound_of_checks 11 stepData011 recoveryData011 rowData011
    transitionCode transition_checks recovery_check_011 row_check_011 move_target_011

private theorem recovery_check_012 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 12 recoveryData012 j = true := by
  have hg : seedIndices 12 = [2, 9, 16, 37, 128] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_012 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 12 recoveryData012 rowData012 b j = true := by
  have hi : seedTransversalPattern 12 = 6 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData012 b j)
     (transitionT c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData012 (rowMember rowData012 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] (rowTarget rowData012 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_012 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData012 j b = rowTarget rowData012 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound012 : MoveSound 12 stepData012 :=
  moveSound_of_checks 12 stepData012 recoveryData012 rowData012
    transitionCode transition_checks recovery_check_012 row_check_012 move_target_012

private theorem recovery_check_013 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 13 recoveryData013 j = true := by
  have hg : seedIndices 13 = [2, 9, 16, 65, 128, 512] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_013 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 13 recoveryData013 rowData013 b j = true := by
  have hi : seedTransversalPattern 13 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData013 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData013 (rowMember rowData013 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData013 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_013 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData013 j b = rowTarget rowData013 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound013 : MoveSound 13 stepData013 :=
  moveSound_of_checks 13 stepData013 recoveryData013 rowData013
    transitionCode transition_checks recovery_check_013 row_check_013 move_target_013

private theorem recovery_check_014 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 14 recoveryData014 j = true := by
  have hg : seedIndices 14 = [2, 9, 16, 65, 128, 513] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_014 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 14 recoveryData014 rowData014 b j = true := by
  have hi : seedTransversalPattern 14 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData014 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData014 (rowMember rowData014 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData014 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_014 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData014 j b = rowTarget rowData014 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound014 : MoveSound 14 stepData014 :=
  moveSound_of_checks 14 stepData014 recoveryData014 rowData014
    transitionCode transition_checks recovery_check_014 row_check_014 move_target_014

private theorem recovery_check_015 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 15 recoveryData015 j = true := by
  have hg : seedIndices 15 = [2, 9, 16, 65, 128, 548] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_015 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 15 recoveryData015 rowData015 b j = true := by
  have hi : seedTransversalPattern 15 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData015 b j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData015 (rowMember rowData015 b j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData015 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_015 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData015 j b = rowTarget rowData015 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound015 : MoveSound 15 stepData015 :=
  moveSound_of_checks 15 stepData015 recoveryData015 rowData015
    transitionCode transition_checks recovery_check_015 row_check_015 move_target_015


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
