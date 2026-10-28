module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 96 through 111

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

private theorem recovery_check_096 : ∀ j : Fin 64,
    recoveryTest 96 recoveryData096 j = true := by
  have hg : seedIndices 96 = [16, 37, 139, 260] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_096 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 96 recoveryData096 rowData096 a j = true := by
  have hi : seedTransversalPattern 96 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData096 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData096 (rowMember rowData096 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData096 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_096 (n : Fin 2048) : Covered 96 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 96 recoveryData096 rowData096
    recovery_check_096 row_check_096 n

private theorem recovery_check_097 : ∀ j : Fin 64,
    recoveryTest 97 recoveryData097 j = true := by
  have hg : seedIndices 97 = [16, 37, 139, 271] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_097 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 97 recoveryData097 rowData097 a j = true := by
  have hi : seedTransversalPattern 97 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData097 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData097 (rowMember rowData097 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData097 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_097 (n : Fin 2048) : Covered 97 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 97 recoveryData097 rowData097
    recovery_check_097 row_check_097 n

private theorem recovery_check_098 : ∀ j : Fin 64,
    recoveryTest 98 recoveryData098 j = true := by
  have hg : seedIndices 98 = [16, 46, 128, 522, 1286] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_098 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 98 recoveryData098 rowData098 a j = true := by
  have hi : seedTransversalPattern 98 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData098 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData098 (rowMember rowData098 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData098 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_098 (n : Fin 2048) : Covered 98 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 98 recoveryData098 rowData098
    recovery_check_098 row_check_098 n

private theorem recovery_check_099 : ∀ j : Fin 64,
    recoveryTest 99 recoveryData099 j = true := by
  have hg : seedIndices 99 = [16, 65, 128, 288, 1026] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_099 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 99 recoveryData099 rowData099 a j = true := by
  have hi : seedTransversalPattern 99 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData099 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData099 (rowMember rowData099 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData099 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_099 (n : Fin 2048) : Covered 99 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 99 recoveryData099 rowData099
    recovery_check_099 row_check_099 n

private theorem recovery_check_100 : ∀ j : Fin 64,
    recoveryTest 100 recoveryData100 j = true := by
  have hg : seedIndices 100 = [16, 65, 128, 290, 1024] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_100 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 100 recoveryData100 rowData100 a j = true := by
  have hi : seedTransversalPattern 100 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData100 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData100 (rowMember rowData100 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData100 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_100 (n : Fin 2048) : Covered 100 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 100 recoveryData100 rowData100
    recovery_check_100 row_check_100 n

private theorem recovery_check_101 : ∀ j : Fin 64,
    recoveryTest 101 recoveryData101 j = true := by
  have hg : seedIndices 101 = [16, 65, 128, 297, 1035] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_101 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 101 recoveryData101 rowData101 a j = true := by
  have hi : seedTransversalPattern 101 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData101 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData101 (rowMember rowData101 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData101 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_101 (n : Fin 2048) : Covered 101 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 101 recoveryData101 rowData101
    recovery_check_101 row_check_101 n

private theorem recovery_check_102 : ∀ j : Fin 64,
    recoveryTest 102 recoveryData102 j = true := by
  have hg : seedIndices 102 = [16, 65, 139, 260, 1068] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_102 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 102 recoveryData102 rowData102 a j = true := by
  have hi : seedTransversalPattern 102 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData102 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData102 (rowMember rowData102 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData102 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_102 (n : Fin 2048) : Covered 102 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 102 recoveryData102 rowData102
    recovery_check_102 row_check_102 n

private theorem recovery_check_103 : ∀ j : Fin 64,
    recoveryTest 103 recoveryData103 j = true := by
  have hg : seedIndices 103 = [16, 65, 139, 271, 1063] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_103 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 103 recoveryData103 rowData103 a j = true := by
  have hi : seedTransversalPattern 103 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData103 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData103 (rowMember rowData103 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData103 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_103 (n : Fin 2048) : Covered 103 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 103 recoveryData103 rowData103
    recovery_check_103 row_check_103 n

private theorem recovery_check_104 : ∀ j : Fin 64,
    recoveryTest 104 recoveryData104 j = true := by
  have hg : seedIndices 104 = [16, 65, 139, 297, 1035] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_104 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 104 recoveryData104 rowData104 a j = true := by
  have hi : seedTransversalPattern 104 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData104 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData104 (rowMember rowData104 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData104 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_104 (n : Fin 2048) : Covered 104 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 104 recoveryData104 rowData104
    recovery_check_104 row_check_104 n

private theorem recovery_check_105 : ∀ j : Fin 64,
    recoveryTest 105 recoveryData105 j = true := by
  have hg : seedIndices 105 = [27, 38, 137, 268] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_105 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 105 recoveryData105 rowData105 a j = true := by
  have hi : seedTransversalPattern 105 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData105 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData105 (rowMember rowData105 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData105 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_105 (n : Fin 2048) : Covered 105 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 105 recoveryData105 rowData105
    recovery_check_105 row_check_105 n

private theorem recovery_check_106 : ∀ j : Fin 64,
    recoveryTest 106 recoveryData106 j = true := by
  have hg : seedIndices 106 = [27, 39, 139, 515, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_106 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 106 recoveryData106 rowData106 a j = true := by
  have hi : seedTransversalPattern 106 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData106 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData106 (rowMember rowData106 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData106 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_106 (n : Fin 2048) : Covered 106 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 106 recoveryData106 rowData106
    recovery_check_106 row_check_106 n

private theorem recovery_check_107 : ∀ j : Fin 64,
    recoveryTest 107 recoveryData107 j = true := by
  have hg : seedIndices 107 = [27, 44, 128, 515, 1295] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_107 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 107 recoveryData107 rowData107 a j = true := by
  have hi : seedTransversalPattern 107 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData107 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData107 (rowMember rowData107 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData107 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_107 (n : Fin 2048) : Covered 107 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 107 recoveryData107 rowData107
    recovery_check_107 row_check_107 n

private theorem recovery_check_108 : ∀ j : Fin 64,
    recoveryTest 108 recoveryData108 j = true := by
  have hg : seedIndices 108 = [27, 44, 128, 520, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_108 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 108 recoveryData108 rowData108 a j = true := by
  have hi : seedTransversalPattern 108 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData108 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData108 (rowMember rowData108 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData108 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_108 (n : Fin 2048) : Covered 108 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 108 recoveryData108 rowData108
    recovery_check_108 row_check_108 n

private theorem recovery_check_109 : ∀ j : Fin 64,
    recoveryTest 109 recoveryData109 j = true := by
  have hg : seedIndices 109 = [27, 45, 137, 268] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_109 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 109 recoveryData109 rowData109 a j = true := by
  have hi : seedTransversalPattern 109 = 21 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData109 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData109 (rowMember rowData109 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039] (rowTarget rowData109 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_109 (n : Fin 2048) : Covered 109 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 109 recoveryData109 rowData109
    recovery_check_109 row_check_109 n

private theorem recovery_check_110 : ∀ j : Fin 64,
    recoveryTest 110 recoveryData110 j = true := by
  have hg : seedIndices 110 = [27, 65, 128, 260, 1063] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_110 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 110 recoveryData110 rowData110 a j = true := by
  have hi : seedTransversalPattern 110 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData110 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData110 (rowMember rowData110 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData110 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_110 (n : Fin 2048) : Covered 110 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 110 recoveryData110 rowData110
    recovery_check_110 row_check_110 n

private theorem recovery_check_111 : ∀ j : Fin 64,
    recoveryTest 111 recoveryData111 j = true := by
  have hg : seedIndices 111 = [27, 65, 128, 271, 1068] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_111 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 111 recoveryData111 rowData111 a j = true := by
  have hi : seedTransversalPattern 111 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData111 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData111 (rowMember rowData111 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData111 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_111 (n : Fin 2048) : Covered 111 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 111 recoveryData111 rowData111
    recovery_check_111 row_check_111 n

theorem coveredBlock096 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨96 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_096 n
  · exact covered_097 n
  · exact covered_098 n
  · exact covered_099 n
  · exact covered_100 n
  · exact covered_101 n
  · exact covered_102 n
  · exact covered_103 n
  · exact covered_104 n
  · exact covered_105 n
  · exact covered_106 n
  · exact covered_107 n
  · exact covered_108 n
  · exact covered_109 n
  · exact covered_110 n
  · exact covered_111 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
