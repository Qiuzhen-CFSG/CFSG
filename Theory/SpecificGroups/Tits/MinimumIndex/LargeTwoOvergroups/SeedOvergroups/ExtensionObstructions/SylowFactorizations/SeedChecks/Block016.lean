module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 16 through 31

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

private theorem recovery_check_016 : ∀ j : Fin 64,
    recoveryTest 16 recoveryData016 j = true := by
  have hg : seedIndices 16 = [2, 9, 16, 65, 128, 1797] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_016 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 16 recoveryData016 rowData016 a j = true := by
  have hi : seedTransversalPattern 16 = 8 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData016 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 512, 513, 516, 517, 544, 545, 548, 549, 768, 769, 772, 773, 800, 801, 804, 805] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData016 (rowMember rowData016 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 512, 513, 516, 517, 544, 545, 548, 549, 768, 769, 772, 773, 800, 801, 804, 805] (rowTarget rowData016 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_016 (n : Fin 2048) : Covered 16 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 16 recoveryData016 rowData016
    recovery_check_016 row_check_016 n

private theorem recovery_check_017 : ∀ j : Fin 64,
    recoveryTest 17 recoveryData017 j = true := by
  have hg : seedIndices 17 = [2, 9, 16, 65, 129, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_017 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 17 recoveryData017 rowData017 a j = true := by
  have hi : seedTransversalPattern 17 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData017 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData017 (rowMember rowData017 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData017 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_017 (n : Fin 2048) : Covered 17 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 17 recoveryData017 rowData017
    recovery_check_017 row_check_017 n

private theorem recovery_check_018 : ∀ j : Fin 64,
    recoveryTest 18 recoveryData018 j = true := by
  have hg : seedIndices 18 = [2, 9, 16, 65, 129, 517] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_018 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 18 recoveryData018 rowData018 a j = true := by
  have hi : seedTransversalPattern 18 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData018 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData018 (rowMember rowData018 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData018 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_018 (n : Fin 2048) : Covered 18 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 18 recoveryData018 rowData018
    recovery_check_018 row_check_018 n

private theorem recovery_check_019 : ∀ j : Fin 64,
    recoveryTest 19 recoveryData019 j = true := by
  have hg : seedIndices 19 = [2, 9, 16, 65, 164, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_019 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 19 recoveryData019 rowData019 a j = true := by
  have hi : seedTransversalPattern 19 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData019 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData019 (rowMember rowData019 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData019 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_019 (n : Fin 2048) : Covered 19 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 19 recoveryData019 rowData019
    recovery_check_019 row_check_019 n

private theorem recovery_check_020 : ∀ j : Fin 64,
    recoveryTest 20 recoveryData020 j = true := by
  have hg : seedIndices 20 = [2, 9, 16, 65, 164, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_020 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 20 recoveryData020 rowData020 a j = true := by
  have hi : seedTransversalPattern 20 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData020 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData020 (rowMember rowData020 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData020 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_020 (n : Fin 2048) : Covered 20 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 20 recoveryData020 rowData020
    recovery_check_020 row_check_020 n

private theorem recovery_check_021 : ∀ j : Fin 64,
    recoveryTest 21 recoveryData021 j = true := by
  have hg : seedIndices 21 = [2, 9, 16, 65, 165, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_021 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 21 recoveryData021 rowData021 a j = true := by
  have hi : seedTransversalPattern 21 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData021 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData021 (rowMember rowData021 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData021 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_021 (n : Fin 2048) : Covered 21 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 21 recoveryData021 rowData021
    recovery_check_021 row_check_021 n

private theorem recovery_check_022 : ∀ j : Fin 64,
    recoveryTest 22 recoveryData022 j = true := by
  have hg : seedIndices 22 = [2, 9, 16, 65, 165, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_022 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 22 recoveryData022 rowData022 a j = true := by
  have hi : seedTransversalPattern 22 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData022 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData022 (rowMember rowData022 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData022 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_022 (n : Fin 2048) : Covered 22 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 22 recoveryData022 rowData022
    recovery_check_022 row_check_022 n

private theorem recovery_check_023 : ∀ j : Fin 64,
    recoveryTest 23 recoveryData023 j = true := by
  have hg : seedIndices 23 = [2, 9, 16, 65, 288] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_023 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 23 recoveryData023 rowData023 a j = true := by
  have hi : seedTransversalPattern 23 = 9 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData023 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData023 (rowMember rowData023 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] (rowTarget rowData023 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_023 (n : Fin 2048) : Covered 23 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 23 recoveryData023 rowData023
    recovery_check_023 row_check_023 n

private theorem recovery_check_024 : ∀ j : Fin 64,
    recoveryTest 24 recoveryData024 j = true := by
  have hg : seedIndices 24 = [2, 9, 16, 65, 289] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_024 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 24 recoveryData024 rowData024 a j = true := by
  have hi : seedTransversalPattern 24 = 9 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData024 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData024 (rowMember rowData024 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 128, 129, 132, 133, 160, 161, 164, 165, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1152, 1153, 1156, 1157, 1184, 1185, 1188, 1189] (rowTarget rowData024 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_024 (n : Fin 2048) : Covered 24 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 24 recoveryData024 rowData024
    recovery_check_024 row_check_024 n

private theorem recovery_check_025 : ∀ j : Fin 64,
    recoveryTest 25 recoveryData025 j = true := by
  have hg : seedIndices 25 = [2, 16, 65, 128, 269] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_025 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 25 recoveryData025 rowData025 a j = true := by
  have hi : seedTransversalPattern 25 = 10 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData025 a j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 1024, 1025, 1028, 1029, 1032, 1033, 1036, 1037, 1056, 1057, 1060, 1061, 1064, 1065, 1068, 1069] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData025 (rowMember rowData025 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 1024, 1025, 1028, 1029, 1032, 1033, 1036, 1037, 1056, 1057, 1060, 1061, 1064, 1065, 1068, 1069] (rowTarget rowData025 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_025 (n : Fin 2048) : Covered 25 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 25 recoveryData025 rowData025
    recovery_check_025 row_check_025 n

private theorem recovery_check_026 : ∀ j : Fin 64,
    recoveryTest 26 recoveryData026 j = true := by
  have hg : seedIndices 26 = [2, 16, 65, 137, 548, 1321] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_026 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 26 recoveryData026 rowData026 a j = true := by
  have hi : seedTransversalPattern 26 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData026 a j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData026 (rowMember rowData026 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData026 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_026 (n : Fin 2048) : Covered 26 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 26 recoveryData026 rowData026
    recovery_check_026 row_check_026 n

private theorem recovery_check_027 : ∀ j : Fin 64,
    recoveryTest 27 recoveryData027 j = true := by
  have hg : seedIndices 27 = [2, 16, 65, 137, 557, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_027 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 27 recoveryData027 rowData027 a j = true := by
  have hi : seedTransversalPattern 27 = 11 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData027 a j)
     (transitionT c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData027 (rowMember rowData027 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 256, 257, 260, 261, 264, 265, 268, 269, 288, 289, 292, 293, 296, 297, 300, 301] (rowTarget rowData027 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_027 (n : Fin 2048) : Covered 27 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 27 recoveryData027 rowData027
    recovery_check_027 row_check_027 n

private theorem recovery_check_028 : ∀ j : Fin 64,
    recoveryTest 28 recoveryData028 j = true := by
  have hg : seedIndices 28 = [3, 4, 16, 64, 129] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_028 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 28 recoveryData028 rowData028 a j = true := by
  have hi : seedTransversalPattern 28 = 12 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData028 a j)
     (transitionT c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData028 (rowMember rowData028 a j)) &&
     (transitionU c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] (rowTarget rowData028 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_028 (n : Fin 2048) : Covered 28 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 28 recoveryData028 rowData028
    recovery_check_028 row_check_028 n

private theorem recovery_check_029 : ∀ j : Fin 64,
    recoveryTest 29 recoveryData029 j = true := by
  have hg : seedIndices 29 = [3, 4, 16, 65, 128] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_029 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 29 recoveryData029 rowData029 a j = true := by
  have hi : seedTransversalPattern 29 = 12 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData029 a j)
     (transitionT c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData029 (rowMember rowData029 a j)) &&
     (transitionU c == ![0, 1, 32, 33, 256, 257, 288, 289, 512, 513, 544, 545, 768, 769, 800, 801, 1024, 1025, 1056, 1057, 1280, 1281, 1312, 1313, 1536, 1537, 1568, 1569, 1792, 1793, 1824, 1825] (rowTarget rowData029 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_029 (n : Fin 2048) : Covered 29 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 29 recoveryData029 rowData029
    recovery_check_029 row_check_029 n

private theorem recovery_check_030 : ∀ j : Fin 64,
    recoveryTest 30 recoveryData030 j = true := by
  have hg : seedIndices 30 = [3, 8, 16, 65, 128, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_030 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 30 recoveryData030 rowData030 a j = true := by
  have hi : seedTransversalPattern 30 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData030 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData030 (rowMember rowData030 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData030 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_030 (n : Fin 2048) : Covered 30 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 30 recoveryData030 rowData030
    recovery_check_030 row_check_030 n

private theorem recovery_check_031 : ∀ j : Fin 64,
    recoveryTest 31 recoveryData031 j = true := by
  have hg : seedIndices 31 = [3, 8, 16, 65, 128, 545] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_031 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 31 recoveryData031 rowData031 a j = true := by
  have hi : seedTransversalPattern 31 = 7 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData031 a j)
     (transitionT c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData031 (rowMember rowData031 a j)) &&
     (transitionU c == ![0, 1, 4, 5, 32, 33, 36, 37, 256, 257, 260, 261, 288, 289, 292, 293, 1024, 1025, 1028, 1029, 1056, 1057, 1060, 1061, 1280, 1281, 1284, 1285, 1312, 1313, 1316, 1317] (rowTarget rowData031 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_031 (n : Fin 2048) : Covered 31 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 31 recoveryData031 rowData031
    recovery_check_031 row_check_031 n

theorem coveredBlock016 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨16 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_016 n
  · exact covered_017 n
  · exact covered_018 n
  · exact covered_019 n
  · exact covered_020 n
  · exact covered_021 n
  · exact covered_022 n
  · exact covered_023 n
  · exact covered_024 n
  · exact covered_025 n
  · exact covered_026 n
  · exact covered_027 n
  · exact covered_028 n
  · exact covered_029 n
  · exact covered_030 n
  · exact covered_031 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
