module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 32 through 47

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

private theorem recovery_check_032 : ∀ j : Fin 64,
    recoveryTest 32 recoveryData032 j = true := by
  have hg : seedIndices 32 = [3, 8, 16, 65, 165, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_032 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 32 recoveryData032 rowData032 a j = true := by
  have hi : seedTransversalPattern 32 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData032 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData032 (rowMember rowData032 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData032 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_032 (n : Fin 2048) : Covered 32 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 32 recoveryData032 rowData032
    recovery_check_032 row_check_032 n

private theorem recovery_check_033 : ∀ j : Fin 64,
    recoveryTest 33 recoveryData033 j = true := by
  have hg : seedIndices 33 = [3, 8, 16, 65, 165, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_033 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 33 recoveryData033 rowData033 a j = true := by
  have hi : seedTransversalPattern 33 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData033 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData033 (rowMember rowData033 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData033 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_033 (n : Fin 2048) : Covered 33 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 33 recoveryData033 rowData033
    recovery_check_033 row_check_033 n

private theorem recovery_check_034 : ∀ j : Fin 64,
    recoveryTest 34 recoveryData034 j = true := by
  have hg : seedIndices 34 = [3, 8, 16, 65, 165, 548] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_034 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 34 recoveryData034 rowData034 a j = true := by
  have hi : seedTransversalPattern 34 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData034 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData034 (rowMember rowData034 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData034 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_034 (n : Fin 2048) : Covered 34 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 34 recoveryData034 rowData034
    recovery_check_034 row_check_034 n

private theorem recovery_check_035 : ∀ j : Fin 64,
    recoveryTest 35 recoveryData035 j = true := by
  have hg : seedIndices 35 = [3, 8, 16, 65, 512, 1313] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_035 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 35 recoveryData035 rowData035 a j = true := by
  have hi : seedTransversalPattern 35 = 13 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData035 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData035 (rowMember rowData035 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] (rowTarget rowData035 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_035 (n : Fin 2048) : Covered 35 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 35 recoveryData035 rowData035
    recovery_check_035 row_check_035 n

private theorem recovery_check_036 : ∀ j : Fin 64,
    recoveryTest 36 recoveryData036 j = true := by
  have hg : seedIndices 36 = [3, 8, 16, 65, 512, 1412] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_036 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 36 recoveryData036 rowData036 a j = true := by
  have hi : seedTransversalPattern 36 = 13 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData036 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData036 (rowMember rowData036 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 256, 257, 260, 261, 288, 289, 292, 293, 384, 385, 388, 389, 416, 417, 420, 421] (rowTarget rowData036 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_036 (n : Fin 2048) : Covered 36 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 36 recoveryData036 rowData036
    recovery_check_036 row_check_036 n

private theorem recovery_check_037 : ∀ j : Fin 64,
    recoveryTest 37 recoveryData037 j = true := by
  have hg : seedIndices 37 = [3, 24, 65, 164, 520, 1313] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_037 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 37 recoveryData037 rowData037 a j = true := by
  have hi : seedTransversalPattern 37 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData037 a j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData037 (rowMember rowData037 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData037 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_037 (n : Fin 2048) : Covered 37 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 37 recoveryData037 rowData037
    recovery_check_037 row_check_037 n

private theorem recovery_check_038 : ∀ j : Fin 64,
    recoveryTest 38 recoveryData038 j = true := by
  have hg : seedIndices 38 = [3, 24, 65, 164, 520, 1321] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_038 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 38 recoveryData038 rowData038 a j = true := by
  have hi : seedTransversalPattern 38 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData038 a j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData038 (rowMember rowData038 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData038 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_038 (n : Fin 2048) : Covered 38 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 38 recoveryData038 rowData038
    recovery_check_038 row_check_038 n

private theorem recovery_check_039 : ∀ j : Fin 64,
    recoveryTest 39 recoveryData039 j = true := by
  have hg : seedIndices 39 = [8, 19, 65, 164, 512, 1313] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_039 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 39 recoveryData039 rowData039 a j = true := by
  have hi : seedTransversalPattern 39 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData039 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData039 (rowMember rowData039 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData039 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_039 (n : Fin 2048) : Covered 39 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 39 recoveryData039 rowData039
    recovery_check_039 row_check_039 n

private theorem recovery_check_040 : ∀ j : Fin 64,
    recoveryTest 40 recoveryData040 j = true := by
  have hg : seedIndices 40 = [8, 19, 65, 164, 512, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_040 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 40 recoveryData040 rowData040 a j = true := by
  have hi : seedTransversalPattern 40 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData040 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData040 (rowMember rowData040 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData040 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_040 (n : Fin 2048) : Covered 40 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 40 recoveryData040 rowData040
    recovery_check_040 row_check_040 n

private theorem recovery_check_041 : ∀ j : Fin 64,
    recoveryTest 41 recoveryData041 j = true := by
  have hg : seedIndices 41 = [9, 16, 65, 130, 262] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_041 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 41 recoveryData041 rowData041 a j = true := by
  have hi : seedTransversalPattern 41 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData041 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData041 (rowMember rowData041 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData041 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_041 (n : Fin 2048) : Covered 41 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 41 recoveryData041 rowData041
    recovery_check_041 row_check_041 n

private theorem recovery_check_042 : ∀ j : Fin 64,
    recoveryTest 42 recoveryData042 j = true := by
  have hg : seedIndices 42 = [9, 16, 65, 130, 548, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_042 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 42 recoveryData042 rowData042 a j = true := by
  have hi : seedTransversalPattern 42 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData042 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData042 (rowMember rowData042 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData042 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_042 (n : Fin 2048) : Covered 42 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 42 recoveryData042 rowData042
    recovery_check_042 row_check_042 n

private theorem recovery_check_043 : ∀ j : Fin 64,
    recoveryTest 43 recoveryData043 j = true := by
  have hg : seedIndices 43 = [9, 18, 65, 130, 548, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_043 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 43 recoveryData043 rowData043 a j = true := by
  have hi : seedTransversalPattern 43 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData043 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData043 (rowMember rowData043 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData043 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_043 (n : Fin 2048) : Covered 43 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 43 recoveryData043 rowData043
    recovery_check_043 row_check_043 n

private theorem recovery_check_044 : ∀ j : Fin 64,
    recoveryTest 44 recoveryData044 j = true := by
  have hg : seedIndices 44 = [9, 18, 65, 130, 550, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_044 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 44 recoveryData044 rowData044 a j = true := by
  have hi : seedTransversalPattern 44 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData044 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData044 (rowMember rowData044 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData044 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_044 (n : Fin 2048) : Covered 44 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 44 recoveryData044 rowData044
    recovery_check_044 row_check_044 n

private theorem recovery_check_045 : ∀ j : Fin 64,
    recoveryTest 45 recoveryData045 j = true := by
  have hg : seedIndices 45 = [9, 18, 65, 130, 550, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_045 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 45 recoveryData045 rowData045 a j = true := by
  have hi : seedTransversalPattern 45 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData045 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData045 (rowMember rowData045 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData045 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_045 (n : Fin 2048) : Covered 45 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 45 recoveryData045 rowData045
    recovery_check_045 row_check_045 n

private theorem recovery_check_046 : ∀ j : Fin 64,
    recoveryTest 46 recoveryData046 j = true := by
  have hg : seedIndices 46 = [11, 16, 36, 128, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_046 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 46 recoveryData046 rowData046 a j = true := by
  have hi : seedTransversalPattern 46 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData046 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData046 (rowMember rowData046 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData046 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_046 (n : Fin 2048) : Covered 46 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 46 recoveryData046 rowData046
    recovery_check_046 row_check_046 n

private theorem recovery_check_047 : ∀ j : Fin 64,
    recoveryTest 47 recoveryData047 j = true := by
  have hg : seedIndices 47 = [11, 16, 36, 128, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_047 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 47 recoveryData047 rowData047 a j = true := by
  have hi : seedTransversalPattern 47 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData047 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData047 (rowMember rowData047 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData047 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_047 (n : Fin 2048) : Covered 47 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 47 recoveryData047 rowData047
    recovery_check_047 row_check_047 n

theorem coveredBlock032 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨32 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_032 n
  · exact covered_033 n
  · exact covered_034 n
  · exact covered_035 n
  · exact covered_036 n
  · exact covered_037 n
  · exact covered_038 n
  · exact covered_039 n
  · exact covered_040 n
  · exact covered_041 n
  · exact covered_042 n
  · exact covered_043 n
  · exact covered_044 n
  · exact covered_045 n
  · exact covered_046 n
  · exact covered_047 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
