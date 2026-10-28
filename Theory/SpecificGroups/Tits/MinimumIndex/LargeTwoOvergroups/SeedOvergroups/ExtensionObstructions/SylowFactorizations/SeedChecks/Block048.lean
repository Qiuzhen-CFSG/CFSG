module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 48 through 63

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

private theorem recovery_check_048 : ∀ j : Fin 64,
    recoveryTest 48 recoveryData048 j = true := by
  have hg : seedIndices 48 = [11, 16, 36, 128, 515] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_048 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 48 recoveryData048 rowData048 a j = true := by
  have hi : seedTransversalPattern 48 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData048 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData048 (rowMember rowData048 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData048 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_048 (n : Fin 2048) : Covered 48 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 48 recoveryData048 rowData048
    recovery_check_048 row_check_048 n

private theorem recovery_check_049 : ∀ j : Fin 64,
    recoveryTest 49 recoveryData049 j = true := by
  have hg : seedIndices 49 = [11, 16, 36, 129, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_049 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 49 recoveryData049 rowData049 a j = true := by
  have hi : seedTransversalPattern 49 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData049 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData049 (rowMember rowData049 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData049 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_049 (n : Fin 2048) : Covered 49 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 49 recoveryData049 rowData049
    recovery_check_049 row_check_049 n

private theorem recovery_check_050 : ∀ j : Fin 64,
    recoveryTest 50 recoveryData050 j = true := by
  have hg : seedIndices 50 = [11, 16, 36, 129, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_050 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 50 recoveryData050 rowData050 a j = true := by
  have hi : seedTransversalPattern 50 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData050 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData050 (rowMember rowData050 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData050 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_050 (n : Fin 2048) : Covered 50 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 50 recoveryData050 rowData050
    recovery_check_050 row_check_050 n

private theorem recovery_check_051 : ∀ j : Fin 64,
    recoveryTest 51 recoveryData051 j = true := by
  have hg : seedIndices 51 = [11, 16, 36, 129, 515] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_051 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 51 recoveryData051 rowData051 a j = true := by
  have hi : seedTransversalPattern 51 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData051 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData051 (rowMember rowData051 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData051 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_051 (n : Fin 2048) : Covered 51 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 51 recoveryData051 rowData051
    recovery_check_051 row_check_051 n

private theorem recovery_check_052 : ∀ j : Fin 64,
    recoveryTest 52 recoveryData052 j = true := by
  have hg : seedIndices 52 = [11, 16, 37, 128, 513] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_052 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 52 recoveryData052 rowData052 a j = true := by
  have hi : seedTransversalPattern 52 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData052 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData052 (rowMember rowData052 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData052 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_052 (n : Fin 2048) : Covered 52 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 52 recoveryData052 rowData052
    recovery_check_052 row_check_052 n

private theorem recovery_check_053 : ∀ j : Fin 64,
    recoveryTest 53 recoveryData053 j = true := by
  have hg : seedIndices 53 = [11, 16, 37, 128, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_053 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 53 recoveryData053 rowData053 a j = true := by
  have hi : seedTransversalPattern 53 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData053 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData053 (rowMember rowData053 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData053 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_053 (n : Fin 2048) : Covered 53 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 53 recoveryData053 rowData053
    recovery_check_053 row_check_053 n

private theorem recovery_check_054 : ∀ j : Fin 64,
    recoveryTest 54 recoveryData054 j = true := by
  have hg : seedIndices 54 = [11, 16, 37, 128, 515] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_054 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 54 recoveryData054 rowData054 a j = true := by
  have hi : seedTransversalPattern 54 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData054 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData054 (rowMember rowData054 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData054 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_054 (n : Fin 2048) : Covered 54 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 54 recoveryData054 rowData054
    recovery_check_054 row_check_054 n

private theorem recovery_check_055 : ∀ j : Fin 64,
    recoveryTest 55 recoveryData055 j = true := by
  have hg : seedIndices 55 = [11, 16, 37, 128, 1797] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_055 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 55 recoveryData055 rowData055 a j = true := by
  have hi : seedTransversalPattern 55 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData055 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData055 (rowMember rowData055 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData055 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_055 (n : Fin 2048) : Covered 55 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 55 recoveryData055 rowData055
    recovery_check_055 row_check_055 n

private theorem recovery_check_056 : ∀ j : Fin 64,
    recoveryTest 56 recoveryData056 j = true := by
  have hg : seedIndices 56 = [11, 16, 38, 130, 512] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_056 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 56 recoveryData056 rowData056 a j = true := by
  have hi : seedTransversalPattern 56 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData056 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData056 (rowMember rowData056 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData056 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_056 (n : Fin 2048) : Covered 56 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 56 recoveryData056 rowData056
    recovery_check_056 row_check_056 n

private theorem recovery_check_057 : ∀ j : Fin 64,
    recoveryTest 57 recoveryData057 j = true := by
  have hg : seedIndices 57 = [11, 16, 38, 130, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_057 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 57 recoveryData057 rowData057 a j = true := by
  have hi : seedTransversalPattern 57 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData057 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData057 (rowMember rowData057 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData057 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_057 (n : Fin 2048) : Covered 57 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 57 recoveryData057 rowData057
    recovery_check_057 row_check_057 n

private theorem recovery_check_058 : ∀ j : Fin 64,
    recoveryTest 58 recoveryData058 j = true := by
  have hg : seedIndices 58 = [11, 16, 38, 131, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_058 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 58 recoveryData058 rowData058 a j = true := by
  have hi : seedTransversalPattern 58 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData058 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData058 (rowMember rowData058 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData058 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_058 (n : Fin 2048) : Covered 58 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 58 recoveryData058 rowData058
    recovery_check_058 row_check_058 n

private theorem recovery_check_059 : ∀ j : Fin 64,
    recoveryTest 59 recoveryData059 j = true := by
  have hg : seedIndices 59 = [11, 16, 39, 128, 1797] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_059 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 59 recoveryData059 rowData059 a j = true := by
  have hi : seedTransversalPattern 59 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData059 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData059 (rowMember rowData059 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData059 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_059 (n : Fin 2048) : Covered 59 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 59 recoveryData059 rowData059
    recovery_check_059 row_check_059 n

private theorem recovery_check_060 : ∀ j : Fin 64,
    recoveryTest 60 recoveryData060 j = true := by
  have hg : seedIndices 60 = [11, 16, 39, 128, 1799] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_060 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 60 recoveryData060 rowData060 a j = true := by
  have hi : seedTransversalPattern 60 = 17 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData060 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData060 (rowMember rowData060 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 512, 513, 514, 515, 516, 517, 518, 519, 768, 769, 770, 771, 772, 773, 774, 775] (rowTarget rowData060 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_060 (n : Fin 2048) : Covered 60 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 60 recoveryData060 rowData060
    recovery_check_060 row_check_060 n

private theorem recovery_check_061 : ∀ j : Fin 64,
    recoveryTest 61 recoveryData061 j = true := by
  have hg : seedIndices 61 = [11, 16, 39, 130, 514] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_061 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 61 recoveryData061 rowData061 a j = true := by
  have hi : seedTransversalPattern 61 = 16 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData061 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData061 (rowMember rowData061 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 256, 257, 258, 259, 260, 261, 262, 263, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287] (rowTarget rowData061 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_061 (n : Fin 2048) : Covered 61 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 61 recoveryData061 rowData061
    recovery_check_061 row_check_061 n

private theorem recovery_check_062 : ∀ j : Fin 64,
    recoveryTest 62 recoveryData062 j = true := by
  have hg : seedIndices 62 = [11, 16, 65, 128, 261] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_062 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 62 recoveryData062 rowData062 a j = true := by
  have hi : seedTransversalPattern 62 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData062 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData062 (rowMember rowData062 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData062 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_062 (n : Fin 2048) : Covered 62 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 62 recoveryData062 rowData062
    recovery_check_062 row_check_062 n

private theorem recovery_check_063 : ∀ j : Fin 64,
    recoveryTest 63 recoveryData063 j = true := by
  have hg : seedIndices 63 = [11, 16, 65, 128, 290] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_063 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 63 recoveryData063 rowData063 a j = true := by
  have hi : seedTransversalPattern 63 = 15 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData063 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData063 (rowMember rowData063 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063] (rowTarget rowData063 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_063 (n : Fin 2048) : Covered 63 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 63 recoveryData063 rowData063
    recovery_check_063 row_check_063 n

theorem coveredBlock048 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨48 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_048 n
  · exact covered_049 n
  · exact covered_050 n
  · exact covered_051 n
  · exact covered_052 n
  · exact covered_053 n
  · exact covered_054 n
  · exact covered_055 n
  · exact covered_056 n
  · exact covered_057 n
  · exact covered_058 n
  · exact covered_059 n
  · exact covered_060 n
  · exact covered_061 n
  · exact covered_062 n
  · exact covered_063 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
