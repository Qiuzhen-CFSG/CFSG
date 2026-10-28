module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 80 through 95

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

private theorem recovery_check_080 : ∀ j : Fin 64,
    recoveryTest 80 recoveryData080 j = true := by
  have hg : seedIndices 80 = [11, 16, 65, 167, 548, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_080 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 80 recoveryData080 rowData080 a j = true := by
  have hi : seedTransversalPattern 80 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData080 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData080 (rowMember rowData080 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData080 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_080 (n : Fin 2048) : Covered 80 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 80 recoveryData080 rowData080
    recovery_check_080 row_check_080 n

private theorem recovery_check_081 : ∀ j : Fin 64,
    recoveryTest 81 recoveryData081 j = true := by
  have hg : seedIndices 81 = [11, 16, 65, 167, 548, 1285] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_081 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 81 recoveryData081 rowData081 a j = true := by
  have hi : seedTransversalPattern 81 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData081 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData081 (rowMember rowData081 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData081 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_081 (n : Fin 2048) : Covered 81 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 81 recoveryData081 rowData081
    recovery_check_081 row_check_081 n

private theorem recovery_check_082 : ∀ j : Fin 64,
    recoveryTest 82 recoveryData082 j = true := by
  have hg : seedIndices 82 = [11, 16, 65, 288, 1061] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_082 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 82 recoveryData082 rowData082 a j = true := by
  have hi : seedTransversalPattern 82 = 18 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData082 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData082 (rowMember rowData082 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] (rowTarget rowData082 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_082 (n : Fin 2048) : Covered 82 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 82 recoveryData082 rowData082
    recovery_check_082 row_check_082 n

private theorem recovery_check_083 : ∀ j : Fin 64,
    recoveryTest 83 recoveryData083 j = true := by
  have hg : seedIndices 83 = [11, 16, 65, 291, 1057] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_083 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 83 recoveryData083 rowData083 a j = true := by
  have hi : seedTransversalPattern 83 = 18 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData083 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData083 (rowMember rowData083 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 128, 129, 130, 131, 132, 133, 134, 135, 160, 161, 162, 163, 164, 165, 166, 167] (rowTarget rowData083 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_083 (n : Fin 2048) : Covered 83 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 83 recoveryData083 rowData083
    recovery_check_083 row_check_083 n

private theorem recovery_check_084 : ∀ j : Fin 64,
    recoveryTest 84 recoveryData084 j = true := by
  have hg : seedIndices 84 = [11, 17, 32, 129, 518] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_084 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 84 recoveryData084 rowData084 a j = true := by
  have hi : seedTransversalPattern 84 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData084 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData084 (rowMember rowData084 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData084 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_084 (n : Fin 2048) : Covered 84 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 84 recoveryData084 rowData084
    recovery_check_084 row_check_084 n

private theorem recovery_check_085 : ∀ j : Fin 64,
    recoveryTest 85 recoveryData085 j = true := by
  have hg : seedIndices 85 = [11, 17, 33, 129, 518] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_085 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 85 recoveryData085 rowData085 a j = true := by
  have hi : seedTransversalPattern 85 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData085 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData085 (rowMember rowData085 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData085 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_085 (n : Fin 2048) : Covered 85 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 85 recoveryData085 rowData085
    recovery_check_085 row_check_085 n

private theorem recovery_check_086 : ∀ j : Fin 64,
    recoveryTest 86 recoveryData086 j = true := by
  have hg : seedIndices 86 = [11, 17, 34, 130, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_086 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 86 recoveryData086 rowData086 a j = true := by
  have hi : seedTransversalPattern 86 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData086 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData086 (rowMember rowData086 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData086 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_086 (n : Fin 2048) : Covered 86 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 86 recoveryData086 rowData086
    recovery_check_086 row_check_086 n

private theorem recovery_check_087 : ∀ j : Fin 64,
    recoveryTest 87 recoveryData087 j = true := by
  have hg : seedIndices 87 = [11, 17, 35, 130, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_087 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 87 recoveryData087 rowData087 a j = true := by
  have hi : seedTransversalPattern 87 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData087 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData087 (rowMember rowData087 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData087 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_087 (n : Fin 2048) : Covered 87 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 87 recoveryData087 rowData087
    recovery_check_087 row_check_087 n

private theorem recovery_check_088 : ∀ j : Fin 64,
    recoveryTest 88 recoveryData088 j = true := by
  have hg : seedIndices 88 = [11, 18, 65, 128, 548, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_088 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 88 recoveryData088 rowData088 a j = true := by
  have hi : seedTransversalPattern 88 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData088 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData088 (rowMember rowData088 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData088 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_088 (n : Fin 2048) : Covered 88 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 88 recoveryData088 rowData088
    recovery_check_088 row_check_088 n

private theorem recovery_check_089 : ∀ j : Fin 64,
    recoveryTest 89 recoveryData089 j = true := by
  have hg : seedIndices 89 = [11, 18, 65, 128, 550, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_089 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 89 recoveryData089 rowData089 a j = true := by
  have hi : seedTransversalPattern 89 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData089 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData089 (rowMember rowData089 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData089 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_089 (n : Fin 2048) : Covered 89 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 89 recoveryData089 rowData089
    recovery_check_089 row_check_089 n

private theorem recovery_check_090 : ∀ j : Fin 64,
    recoveryTest 90 recoveryData090 j = true := by
  have hg : seedIndices 90 = [11, 65, 128, 290, 1040] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_090 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 90 recoveryData090 rowData090 a j = true := by
  have hi : seedTransversalPattern 90 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData090 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData090 (rowMember rowData090 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData090 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_090 (n : Fin 2048) : Covered 90 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 90 recoveryData090 rowData090
    recovery_check_090 row_check_090 n

private theorem recovery_check_091 : ∀ j : Fin 64,
    recoveryTest 91 recoveryData091 j = true := by
  have hg : seedIndices 91 = [11, 65, 144, 260, 1079] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_091 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 91 recoveryData091 rowData091 a j = true := by
  have hi : seedTransversalPattern 91 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData091 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData091 (rowMember rowData091 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData091 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_091 (n : Fin 2048) : Covered 91 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 91 recoveryData091 rowData091
    recovery_check_091 row_check_091 n

private theorem recovery_check_092 : ∀ j : Fin 64,
    recoveryTest 92 recoveryData092 j = true := by
  have hg : seedIndices 92 = [11, 65, 144, 288, 1042] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_092 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 92 recoveryData092 rowData092 a j = true := by
  have hi : seedTransversalPattern 92 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData092 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData092 (rowMember rowData092 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData092 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_092 (n : Fin 2048) : Covered 92 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 92 recoveryData092 rowData092
    recovery_check_092 row_check_092 n

private theorem recovery_check_093 : ∀ j : Fin 64,
    recoveryTest 93 recoveryData093 j = true := by
  have hg : seedIndices 93 = [11, 65, 144, 306, 1024] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_093 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 93 recoveryData093 rowData093 a j = true := by
  have hi : seedTransversalPattern 93 = 19 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData093 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData093 (rowMember rowData093 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55] (rowTarget rowData093 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_093 (n : Fin 2048) : Covered 93 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 93 recoveryData093 rowData093
    recovery_check_093 row_check_093 n

private theorem recovery_check_094 : ∀ j : Fin 64,
    recoveryTest 94 recoveryData094 j = true := by
  have hg : seedIndices 94 = [16, 37, 128, 513, 1293] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_094 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 94 recoveryData094 rowData094 a j = true := by
  have hi : seedTransversalPattern 94 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData094 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData094 (rowMember rowData094 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData094 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_094 (n : Fin 2048) : Covered 94 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 94 recoveryData094 rowData094
    recovery_check_094 row_check_094 n

private theorem recovery_check_095 : ∀ j : Fin 64,
    recoveryTest 95 recoveryData095 j = true := by
  have hg : seedIndices 95 = [16, 37, 128, 522, 1286] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_095 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 95 recoveryData095 rowData095 a j = true := by
  have hi : seedTransversalPattern 95 = 20 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData095 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData095 (rowMember rowData095 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271] (rowTarget rowData095 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_095 (n : Fin 2048) : Covered 95 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 95 recoveryData095 rowData095
    recovery_check_095 row_check_095 n

theorem coveredBlock080 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨80 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_080 n
  · exact covered_081 n
  · exact covered_082 n
  · exact covered_083 n
  · exact covered_084 n
  · exact covered_085 n
  · exact covered_086 n
  · exact covered_087 n
  · exact covered_088 n
  · exact covered_089 n
  · exact covered_090 n
  · exact covered_091 n
  · exact covered_092 n
  · exact covered_093 n
  · exact covered_094 n
  · exact covered_095 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
