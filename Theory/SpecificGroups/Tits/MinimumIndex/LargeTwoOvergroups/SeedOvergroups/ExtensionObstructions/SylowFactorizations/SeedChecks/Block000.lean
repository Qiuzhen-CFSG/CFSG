module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 0 through 15

Positive recovery trees certify actual seed membership. The reference
checks retain the literal seed generators and transversal. Each fixed
selector is reduced once by a kernel-checked equality before checking
the row. Bounded blocks and sequential declaration elaboration avoid
the measured memory growth of the monolithic certificate module.

Source: Parrott (1972), section 5, p.683; the candidate JSON in
`ExtensionObstructions/source/`. Reproduce with `source/generate.py`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate

set_option Elab.async false

private theorem recovery_check_000 : ∀ j : Fin 64,
    recoveryTest 0 recoveryData000 j = true := by
  have hg : seedIndices 0 = [1, 2, 4, 16, 64] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_000 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 0 recoveryData000 rowData000 a j = true := by
  have hi : seedTransversalPattern 0 = 0 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData000 a j)
     (transitionT c == ![0, 32, 128, 160, 256, 288, 384, 416, 512, 544, 640, 672, 768, 800, 896, 928, 1024, 1056, 1152, 1184, 1280, 1312, 1408, 1440, 1536, 1568, 1664, 1696, 1792, 1824, 1920, 1952] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData000 (rowMember rowData000 a j)) &&
     (transitionU c == ![0, 32, 128, 160, 256, 288, 384, 416, 512, 544, 640, 672, 768, 800, 896, 928, 1024, 1056, 1152, 1184, 1280, 1312, 1408, 1440, 1536, 1568, 1664, 1696, 1792, 1824, 1920, 1952] (rowTarget rowData000 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_000 (n : Fin 2048) : Covered 0 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 0 recoveryData000 rowData000
    recovery_check_000 row_check_000 n

private theorem recovery_check_001 : ∀ j : Fin 64,
    recoveryTest 1 recoveryData001 j = true := by
  have hg : seedIndices 1 = [1, 2, 4, 16, 160] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_001 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 1 recoveryData001 rowData001 a j = true := by
  have hi : seedTransversalPattern 1 = 1 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData001 a j)
     (transitionT c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData001 (rowMember rowData001 a j)) &&
     (transitionU c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] (rowTarget rowData001 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_001 (n : Fin 2048) : Covered 1 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 1 recoveryData001 rowData001
    recovery_check_001 row_check_001 n

private theorem recovery_check_002 : ∀ j : Fin 64,
    recoveryTest 2 recoveryData002 j = true := by
  have hg : seedIndices 2 = [1, 2, 4, 16, 192] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_002 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 2 recoveryData002 rowData002 a j = true := by
  have hi : seedTransversalPattern 2 = 1 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData002 a j)
     (transitionT c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData002 (rowMember rowData002 a j)) &&
     (transitionU c == ![0, 32, 64, 96, 256, 288, 320, 352, 512, 544, 576, 608, 768, 800, 832, 864, 1024, 1056, 1088, 1120, 1280, 1312, 1344, 1376, 1536, 1568, 1600, 1632, 1792, 1824, 1856, 1888] (rowTarget rowData002 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_002 (n : Fin 2048) : Covered 2 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 2 recoveryData002 rowData002
    recovery_check_002 row_check_002 n

private theorem recovery_check_003 : ∀ j : Fin 64,
    recoveryTest 3 recoveryData003 j = true := by
  have hg : seedIndices 3 = [1, 2, 8, 16, 64, 164] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_003 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 3 recoveryData003 rowData003 a j = true := by
  have hi : seedTransversalPattern 3 = 2 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData003 a j)
     (transitionT c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData003 (rowMember rowData003 a j)) &&
     (transitionU c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] (rowTarget rowData003 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_003 (n : Fin 2048) : Covered 3 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 3 recoveryData003 rowData003
    recovery_check_003 row_check_003 n

private theorem recovery_check_004 : ∀ j : Fin 64,
    recoveryTest 4 recoveryData004 j = true := by
  have hg : seedIndices 4 = [1, 2, 8, 16, 64, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_004 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 4 recoveryData004 rowData004 a j = true := by
  have hi : seedTransversalPattern 4 = 3 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData004 a j)
     (transitionT c == ![0, 4, 32, 36, 128, 132, 160, 164, 256, 260, 288, 292, 384, 388, 416, 420, 1024, 1028, 1056, 1060, 1152, 1156, 1184, 1188, 1280, 1284, 1312, 1316, 1408, 1412, 1440, 1444] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData004 (rowMember rowData004 a j)) &&
     (transitionU c == ![0, 4, 32, 36, 128, 132, 160, 164, 256, 260, 288, 292, 384, 388, 416, 420, 1024, 1028, 1056, 1060, 1152, 1156, 1184, 1188, 1280, 1284, 1312, 1316, 1408, 1412, 1440, 1444] (rowTarget rowData004 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_004 (n : Fin 2048) : Covered 4 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 4 recoveryData004 rowData004
    recovery_check_004 row_check_004 n

private theorem recovery_check_005 : ∀ j : Fin 64,
    recoveryTest 5 recoveryData005 j = true := by
  have hg : seedIndices 5 = [1, 2, 8, 16, 68, 164] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_005 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 5 recoveryData005 rowData005 a j = true := by
  have hi : seedTransversalPattern 5 = 2 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData005 a j)
     (transitionT c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData005 (rowMember rowData005 a j)) &&
     (transitionU c == ![0, 4, 32, 36, 256, 260, 288, 292, 512, 516, 544, 548, 768, 772, 800, 804, 1024, 1028, 1056, 1060, 1280, 1284, 1312, 1316, 1536, 1540, 1568, 1572, 1792, 1796, 1824, 1828] (rowTarget rowData005 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_005 (n : Fin 2048) : Covered 5 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 5 recoveryData005 rowData005
    recovery_check_005 row_check_005 n

private theorem recovery_check_006 : ∀ j : Fin 64,
    recoveryTest 6 recoveryData006 j = true := by
  have hg : seedIndices 6 = [1, 10, 16, 34, 130] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_006 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 6 recoveryData006 rowData006 a j = true := by
  have hi : seedTransversalPattern 6 = 4 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData006 a j)
     (transitionT c == ![0, 2, 4, 6, 256, 258, 260, 262, 512, 514, 516, 518, 768, 770, 772, 774, 1024, 1026, 1028, 1030, 1280, 1282, 1284, 1286, 1536, 1538, 1540, 1542, 1792, 1794, 1796, 1798] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData006 (rowMember rowData006 a j)) &&
     (transitionU c == ![0, 2, 4, 6, 256, 258, 260, 262, 512, 514, 516, 518, 768, 770, 772, 774, 1024, 1026, 1028, 1030, 1280, 1282, 1284, 1286, 1536, 1538, 1540, 1542, 1792, 1794, 1796, 1798] (rowTarget rowData006 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_006 (n : Fin 2048) : Covered 6 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 6 recoveryData006 rowData006
    recovery_check_006 row_check_006 n

private theorem recovery_check_007 : ∀ j : Fin 64,
    recoveryTest 7 recoveryData007 j = true := by
  have hg : seedIndices 7 = [1, 10, 16, 64, 130, 546] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_007 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 7 recoveryData007 rowData007 a j = true := by
  have hi : seedTransversalPattern 7 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData007 a j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData007 (rowMember rowData007 a j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData007 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_007 (n : Fin 2048) : Covered 7 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 7 recoveryData007 rowData007
    recovery_check_007 row_check_007 n

private theorem recovery_check_008 : ∀ j : Fin 64,
    recoveryTest 8 recoveryData008 j = true := by
  have hg : seedIndices 8 = [1, 10, 16, 64, 164, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_008 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 8 recoveryData008 rowData008 a j = true := by
  have hi : seedTransversalPattern 8 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData008 a j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData008 (rowMember rowData008 a j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData008 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_008 (n : Fin 2048) : Covered 8 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 8 recoveryData008 rowData008
    recovery_check_008 row_check_008 n

private theorem recovery_check_009 : ∀ j : Fin 64,
    recoveryTest 9 recoveryData009 j = true := by
  have hg : seedIndices 9 = [1, 10, 16, 64, 164, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_009 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 9 recoveryData009 rowData009 a j = true := by
  have hi : seedTransversalPattern 9 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData009 a j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData009 (rowMember rowData009 a j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData009 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_009 (n : Fin 2048) : Covered 9 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 9 recoveryData009 rowData009
    recovery_check_009 row_check_009 n

private theorem recovery_check_010 : ∀ j : Fin 64,
    recoveryTest 10 recoveryData010 j = true := by
  have hg : seedIndices 10 = [1, 10, 16, 64, 164, 548] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_010 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 10 recoveryData010 rowData010 a j = true := by
  have hi : seedTransversalPattern 10 = 5 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData010 a j)
     (transitionT c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData010 (rowMember rowData010 a j)) &&
     (transitionU c == ![0, 2, 4, 6, 32, 34, 36, 38, 256, 258, 260, 262, 288, 290, 292, 294, 1024, 1026, 1028, 1030, 1056, 1058, 1060, 1062, 1280, 1282, 1284, 1286, 1312, 1314, 1316, 1318] (rowTarget rowData010 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_010 (n : Fin 2048) : Covered 10 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 10 recoveryData010 rowData010
    recovery_check_010 row_check_010 n

private theorem recovery_check_011 : ∀ j : Fin 64,
    recoveryTest 11 recoveryData011 j = true := by
  have hg : seedIndices 11 = [2, 9, 16, 36, 128] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_011 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 11 recoveryData011 rowData011 a j = true := by
  have hi : seedTransversalPattern 11 = 6 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData011 a j)
     (transitionT c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData011 (rowMember rowData011 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] (rowTarget rowData011 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_011 (n : Fin 2048) : Covered 11 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 11 recoveryData011 rowData011
    recovery_check_011 row_check_011 n

private theorem recovery_check_012 : ∀ j : Fin 64,
    recoveryTest 12 recoveryData012 j = true := by
  have hg : seedIndices 12 = [2, 9, 16, 37, 128] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_012 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 12 recoveryData012 rowData012 a j = true := by
  have hi : seedTransversalPattern 12 = 6 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData012 a j)
     (transitionT c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData012 (rowMember rowData012 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 256, 257, 260, 261, 512, 513, 516, 517, 768, 769, 772, 773, 1024, 1025, 1028, 1029, 1280, 1281, 1284, 1285, 1536, 1537, 1540, 1541, 1792, 1793, 1796, 1797] (rowTarget rowData012 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_012 (n : Fin 2048) : Covered 12 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 12 recoveryData012 rowData012
    recovery_check_012 row_check_012 n

private theorem recovery_check_013 : ∀ j : Fin 64,
    recoveryTest 13 recoveryData013 j = true := by
  have hg : seedIndices 13 = [2, 9, 16, 65, 128, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_013 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 13 recoveryData013 rowData013 a j = true := by
  have hi : seedTransversalPattern 13 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData013 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData013 (rowMember rowData013 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData013 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_013 (n : Fin 2048) : Covered 13 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 13 recoveryData013 rowData013
    recovery_check_013 row_check_013 n

private theorem recovery_check_014 : ∀ j : Fin 64,
    recoveryTest 14 recoveryData014 j = true := by
  have hg : seedIndices 14 = [2, 9, 16, 65, 128, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_014 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 14 recoveryData014 rowData014 a j = true := by
  have hi : seedTransversalPattern 14 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData014 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData014 (rowMember rowData014 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData014 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_014 (n : Fin 2048) : Covered 14 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 14 recoveryData014 rowData014
    recovery_check_014 row_check_014 n

private theorem recovery_check_015 : ∀ j : Fin 64,
    recoveryTest 15 recoveryData015 j = true := by
  have hg : seedIndices 15 = [2, 9, 16, 65, 128, 548] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_015 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 15 recoveryData015 rowData015 a j = true := by
  have hi : seedTransversalPattern 15 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData015 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData015 (rowMember rowData015 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData015 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_015 (n : Fin 2048) : Covered 15 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 15 recoveryData015 rowData015
    recovery_check_015 row_check_015 n

theorem coveredBlock000 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨0 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_000 n
  · exact covered_001 n
  · exact covered_002 n
  · exact covered_003 n
  · exact covered_004 n
  · exact covered_005 n
  · exact covered_006 n
  · exact covered_007 n
  · exact covered_008 n
  · exact covered_009 n
  · exact covered_010 n
  · exact covered_011 n
  · exact covered_012 n
  · exact covered_013 n
  · exact covered_014 n
  · exact covered_015 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
