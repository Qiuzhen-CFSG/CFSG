module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 64 through 79

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

private theorem recovery_check_064 : ∀ j : Fin 64,
    recoveryTest 64 recoveryData064 j = true := by
  have hg : seedIndices 64 = [11, 16, 65, 128, 513, 1286] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_064 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 64 recoveryData064 rowData064 a j = true := by
  have hi : seedTransversalPattern 64 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData064 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData064 (rowMember rowData064 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData064 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_064 (n : Fin 2048) : Covered 64 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 64 recoveryData064 rowData064
    recovery_check_064 row_check_064 n

private theorem recovery_check_065 : ∀ j : Fin 64,
    recoveryTest 65 recoveryData065 j = true := by
  have hg : seedIndices 65 = [11, 16, 65, 128, 515, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_065 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 65 recoveryData065 rowData065 a j = true := by
  have hi : seedTransversalPattern 65 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData065 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData065 (rowMember rowData065 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData065 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_065 (n : Fin 2048) : Covered 65 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 65 recoveryData065 rowData065
    recovery_check_065 row_check_065 n

private theorem recovery_check_066 : ∀ j : Fin 64,
    recoveryTest 66 recoveryData066 j = true := by
  have hg : seedIndices 66 = [11, 16, 65, 128, 515, 1285] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_066 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 66 recoveryData066 rowData066 a j = true := by
  have hi : seedTransversalPattern 66 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData066 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData066 (rowMember rowData066 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData066 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_066 (n : Fin 2048) : Covered 66 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 66 recoveryData066 rowData066
    recovery_check_066 row_check_066 n

private theorem recovery_check_067 : ∀ j : Fin 64,
    recoveryTest 67 recoveryData067 j = true := by
  have hg : seedIndices 67 = [11, 16, 65, 128, 515, 1286] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_067 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 67 recoveryData067 rowData067 a j = true := by
  have hi : seedTransversalPattern 67 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData067 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData067 (rowMember rowData067 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData067 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_067 (n : Fin 2048) : Covered 67 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 67 recoveryData067 rowData067
    recovery_check_067 row_check_067 n

private theorem recovery_check_068 : ∀ j : Fin 64,
    recoveryTest 68 recoveryData068 j = true := by
  have hg : seedIndices 68 = [11, 16, 65, 128, 515, 1287] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_068 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 68 recoveryData068 rowData068 a j = true := by
  have hi : seedTransversalPattern 68 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData068 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData068 (rowMember rowData068 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData068 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_068 (n : Fin 2048) : Covered 68 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 68 recoveryData068 rowData068
    recovery_check_068 row_check_068 n

private theorem recovery_check_069 : ∀ j : Fin 64,
    recoveryTest 69 recoveryData069 j = true := by
  have hg : seedIndices 69 = [11, 16, 65, 128, 548, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_069 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 69 recoveryData069 rowData069 a j = true := by
  have hi : seedTransversalPattern 69 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData069 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData069 (rowMember rowData069 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData069 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_069 (n : Fin 2048) : Covered 69 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 69 recoveryData069 rowData069
    recovery_check_069 row_check_069 n

private theorem recovery_check_070 : ∀ j : Fin 64,
    recoveryTest 70 recoveryData070 j = true := by
  have hg : seedIndices 70 = [11, 16, 65, 128, 548, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_070 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 70 recoveryData070 rowData070 a j = true := by
  have hi : seedTransversalPattern 70 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData070 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData070 (rowMember rowData070 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData070 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_070 (n : Fin 2048) : Covered 70 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 70 recoveryData070 rowData070
    recovery_check_070 row_check_070 n

private theorem recovery_check_071 : ∀ j : Fin 64,
    recoveryTest 71 recoveryData071 j = true := by
  have hg : seedIndices 71 = [11, 16, 65, 128, 550, 1312] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_071 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 71 recoveryData071 rowData071 a j = true := by
  have hi : seedTransversalPattern 71 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData071 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData071 (rowMember rowData071 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData071 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_071 (n : Fin 2048) : Covered 71 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 71 recoveryData071 rowData071
    recovery_check_071 row_check_071 n

private theorem recovery_check_072 : ∀ j : Fin 64,
    recoveryTest 72 recoveryData072 j = true := by
  have hg : seedIndices 72 = [11, 16, 65, 129, 514, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_072 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 72 recoveryData072 rowData072 a j = true := by
  have hi : seedTransversalPattern 72 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData072 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData072 (rowMember rowData072 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData072 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_072 (n : Fin 2048) : Covered 72 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 72 recoveryData072 rowData072
    recovery_check_072 row_check_072 n

private theorem recovery_check_073 : ∀ j : Fin 64,
    recoveryTest 73 recoveryData073 j = true := by
  have hg : seedIndices 73 = [11, 16, 65, 129, 514, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_073 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 73 recoveryData073 rowData073 a j = true := by
  have hi : seedTransversalPattern 73 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData073 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData073 (rowMember rowData073 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData073 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_073 (n : Fin 2048) : Covered 73 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 73 recoveryData073 rowData073
    recovery_check_073 row_check_073 n

private theorem recovery_check_074 : ∀ j : Fin 64,
    recoveryTest 74 recoveryData074 j = true := by
  have hg : seedIndices 74 = [11, 16, 65, 164, 515, 1313] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_074 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 74 recoveryData074 rowData074 a j = true := by
  have hi : seedTransversalPattern 74 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData074 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData074 (rowMember rowData074 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData074 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_074 (n : Fin 2048) : Covered 74 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 74 recoveryData074 rowData074
    recovery_check_074 row_check_074 n

private theorem recovery_check_075 : ∀ j : Fin 64,
    recoveryTest 75 recoveryData075 j = true := by
  have hg : seedIndices 75 = [11, 16, 65, 164, 515, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_075 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 75 recoveryData075 rowData075 a j = true := by
  have hi : seedTransversalPattern 75 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData075 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData075 (rowMember rowData075 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData075 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_075 (n : Fin 2048) : Covered 75 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 75 recoveryData075 rowData075
    recovery_check_075 row_check_075 n

private theorem recovery_check_076 : ∀ j : Fin 64,
    recoveryTest 76 recoveryData076 j = true := by
  have hg : seedIndices 76 = [11, 16, 65, 166, 549, 1284] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_076 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 76 recoveryData076 rowData076 a j = true := by
  have hi : seedTransversalPattern 76 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData076 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData076 (rowMember rowData076 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData076 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_076 (n : Fin 2048) : Covered 76 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 76 recoveryData076 rowData076
    recovery_check_076 row_check_076 n

private theorem recovery_check_077 : ∀ j : Fin 64,
    recoveryTest 77 recoveryData077 j = true := by
  have hg : seedIndices 77 = [11, 16, 65, 166, 549, 1285] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_077 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 77 recoveryData077 rowData077 a j = true := by
  have hi : seedTransversalPattern 77 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData077 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData077 (rowMember rowData077 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData077 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_077 (n : Fin 2048) : Covered 77 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 77 recoveryData077 rowData077
    recovery_check_077 row_check_077 n

private theorem recovery_check_078 : ∀ j : Fin 64,
    recoveryTest 78 recoveryData078 j = true := by
  have hg : seedIndices 78 = [11, 16, 65, 167, 515, 1313] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_078 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 78 recoveryData078 rowData078 a j = true := by
  have hi : seedTransversalPattern 78 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData078 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData078 (rowMember rowData078 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData078 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_078 (n : Fin 2048) : Covered 78 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 78 recoveryData078 rowData078
    recovery_check_078 row_check_078 n

private theorem recovery_check_079 : ∀ j : Fin 64,
    recoveryTest 79 recoveryData079 j = true := by
  have hg : seedIndices 79 = [11, 16, 65, 167, 515, 1314] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_079 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 79 recoveryData079 rowData079 a j = true := by
  have hi : seedTransversalPattern 79 = 14 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData079 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData079 (rowMember rowData079 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 32, 33, 34, 35, 36, 37, 38, 39, 256, 257, 258, 259, 260, 261, 262, 263, 288, 289, 290, 291, 292, 293, 294, 295] (rowTarget rowData079 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_079 (n : Fin 2048) : Covered 79 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 79 recoveryData079 rowData079
    recovery_check_079 row_check_079 n

theorem coveredBlock064 (i : Fin 16) (n : Fin 2048) :
    Covered ⟨64 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_064 n
  · exact covered_065 n
  · exact covered_066 n
  · exact covered_067 n
  · exact covered_068 n
  · exact covered_069 n
  · exact covered_070 n
  · exact covered_071 n
  · exact covered_072 n
  · exact covered_073 n
  · exact covered_074 n
  · exact covered_075 n
  · exact covered_076 n
  · exact covered_077 n
  · exact covered_078 n
  · exact covered_079 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
