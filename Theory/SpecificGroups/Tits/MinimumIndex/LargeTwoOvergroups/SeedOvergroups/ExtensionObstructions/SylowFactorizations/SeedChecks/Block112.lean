module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Seed factorization certificates 112 through 121

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

private theorem recovery_check_112 : ∀ j : Fin 64,
    recoveryTest 112 recoveryData112 j = true := by
  have hg : seedIndices 112 = [27, 65, 128, 290, 1035] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_112 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 112 recoveryData112 rowData112 a j = true := by
  have hi : seedTransversalPattern 112 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData112 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData112 (rowMember rowData112 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData112 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_112 (n : Fin 2048) : Covered 112 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 112 recoveryData112 rowData112
    recovery_check_112 row_check_112 n

private theorem recovery_check_113 : ∀ j : Fin 64,
    recoveryTest 113 recoveryData113 j = true := by
  have hg : seedIndices 113 = [27, 65, 128, 297, 1024] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_113 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 113 recoveryData113 rowData113 a j = true := by
  have hi : seedTransversalPattern 113 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData113 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData113 (rowMember rowData113 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData113 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_113 (n : Fin 2048) : Covered 113 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 113 recoveryData113 rowData113
    recovery_check_113 row_check_113 n

private theorem recovery_check_114 : ∀ j : Fin 64,
    recoveryTest 114 recoveryData114 j = true := by
  have hg : seedIndices 114 = [27, 65, 139, 288, 1026] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_114 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 114 recoveryData114 rowData114 a j = true := by
  have hi : seedTransversalPattern 114 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData114 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData114 (rowMember rowData114 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData114 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_114 (n : Fin 2048) : Covered 114 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 114 recoveryData114 rowData114
    recovery_check_114 row_check_114 n

private theorem recovery_check_115 : ∀ j : Fin 64,
    recoveryTest 115 recoveryData115 j = true := by
  have hg : seedIndices 115 = [27, 65, 139, 288, 1033] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_115 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 115 recoveryData115 rowData115 a j = true := by
  have hi : seedTransversalPattern 115 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData115 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData115 (rowMember rowData115 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData115 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_115 (n : Fin 2048) : Covered 115 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 115 recoveryData115 rowData115
    recovery_check_115 row_check_115 n

private theorem recovery_check_116 : ∀ j : Fin 64,
    recoveryTest 116 recoveryData116 j = true := by
  have hg : seedIndices 116 = [27, 65, 139, 290, 1026] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_116 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 116 recoveryData116 rowData116 a j = true := by
  have hi : seedTransversalPattern 116 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData116 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData116 (rowMember rowData116 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData116 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_116 (n : Fin 2048) : Covered 116 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 116 recoveryData116 rowData116
    recovery_check_116 row_check_116 n

private theorem recovery_check_117 : ∀ j : Fin 64,
    recoveryTest 117 recoveryData117 j = true := by
  have hg : seedIndices 117 = [27, 65, 139, 297, 1024] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_117 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 117 recoveryData117 rowData117 a j = true := by
  have hi : seedTransversalPattern 117 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData117 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData117 (rowMember rowData117 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData117 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_117 (n : Fin 2048) : Covered 117 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 117 recoveryData117 rowData117
    recovery_check_117 row_check_117 n

private theorem recovery_check_118 : ∀ j : Fin 64,
    recoveryTest 118 recoveryData118 j = true := by
  have hg : seedIndices 118 = [27, 65, 139, 297, 1033] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_118 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 118 recoveryData118 rowData118 a j = true := by
  have hi : seedTransversalPattern 118 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData118 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData118 (rowMember rowData118 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData118 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_118 (n : Fin 2048) : Covered 118 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 118 recoveryData118 rowData118
    recovery_check_118 row_check_118 n

private theorem recovery_check_119 : ∀ j : Fin 64,
    recoveryTest 119 recoveryData119 j = true := by
  have hg : seedIndices 119 = [27, 65, 139, 297, 1035] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_119 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 119 recoveryData119 rowData119 a j = true := by
  have hi : seedTransversalPattern 119 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData119 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData119 (rowMember rowData119 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData119 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_119 (n : Fin 2048) : Covered 119 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 119 recoveryData119 rowData119
    recovery_check_119 row_check_119 n

private theorem recovery_check_120 : ∀ j : Fin 64,
    recoveryTest 120 recoveryData120 j = true := by
  have hg : seedIndices 120 = [27, 65, 139, 299, 1026] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_120 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 120 recoveryData120 rowData120 a j = true := by
  have hi : seedTransversalPattern 120 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData120 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData120 (rowMember rowData120 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData120 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_120 (n : Fin 2048) : Covered 120 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 120 recoveryData120 rowData120
    recovery_check_120 row_check_120 n

private theorem recovery_check_121 : ∀ j : Fin 64,
    recoveryTest 121 recoveryData121 j = true := by
  have hg : seedIndices 121 = [27, 65, 139, 299, 1033] := by decide +kernel
  simp only [recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_121 : ∀ (a : Fin 32) (j : Fin 8),
    rowTest transitionCode 121 recoveryData121 rowData121 a j = true := by
  have hi : seedTransversalPattern 121 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (a : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData121 a j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] a) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData121 (rowMember rowData121 a j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData121 a j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem covered_121 (n : Fin 2048) : Covered 121 (atlas1600SylowTwoNormalForm n) :=
  row_covered transitionCode transition_checks 121 recoveryData121 rowData121
    recovery_check_121 row_check_121 n

theorem coveredBlock112 (i : Fin 10) (n : Fin 2048) :
    Covered ⟨112 + i.val, by omega⟩ (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact covered_112 n
  · exact covered_113 n
  · exact covered_114 n
  · exact covered_115 n
  · exact covered_116 n
  · exact covered_117 n
  · exact covered_118 n
  · exact covered_119 n
  · exact covered_120 n
  · exact covered_121 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
