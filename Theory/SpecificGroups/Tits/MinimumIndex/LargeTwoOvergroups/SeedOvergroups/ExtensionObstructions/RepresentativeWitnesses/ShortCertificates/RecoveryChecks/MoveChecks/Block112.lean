module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.RecoveryChecks.Data
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedData
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.TransitionChecks

/-!
# Sound generator actions for seeds 112 through 121

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

private theorem recovery_check_112 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 112 recoveryData112 j = true := by
  have hg : seedIndices 112 = [27, 65, 128, 290, 1035] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_112 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 112 recoveryData112 rowData112 b j = true := by
  have hi : seedTransversalPattern 112 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData112 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData112 (rowMember rowData112 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData112 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_112 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData112 j b = rowTarget rowData112 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound112 : MoveSound 112 stepData112 :=
  moveSound_of_checks 112 stepData112 recoveryData112 rowData112
    transitionCode transition_checks recovery_check_112 row_check_112 move_target_112

private theorem recovery_check_113 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 113 recoveryData113 j = true := by
  have hg : seedIndices 113 = [27, 65, 128, 297, 1024] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_113 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 113 recoveryData113 rowData113 b j = true := by
  have hi : seedTransversalPattern 113 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData113 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData113 (rowMember rowData113 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData113 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_113 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData113 j b = rowTarget rowData113 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound113 : MoveSound 113 stepData113 :=
  moveSound_of_checks 113 stepData113 recoveryData113 rowData113
    transitionCode transition_checks recovery_check_113 row_check_113 move_target_113

private theorem recovery_check_114 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 114 recoveryData114 j = true := by
  have hg : seedIndices 114 = [27, 65, 139, 288, 1026] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_114 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 114 recoveryData114 rowData114 b j = true := by
  have hi : seedTransversalPattern 114 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData114 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData114 (rowMember rowData114 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData114 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_114 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData114 j b = rowTarget rowData114 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound114 : MoveSound 114 stepData114 :=
  moveSound_of_checks 114 stepData114 recoveryData114 rowData114
    transitionCode transition_checks recovery_check_114 row_check_114 move_target_114

private theorem recovery_check_115 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 115 recoveryData115 j = true := by
  have hg : seedIndices 115 = [27, 65, 139, 288, 1033] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_115 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 115 recoveryData115 rowData115 b j = true := by
  have hi : seedTransversalPattern 115 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData115 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData115 (rowMember rowData115 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData115 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_115 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData115 j b = rowTarget rowData115 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound115 : MoveSound 115 stepData115 :=
  moveSound_of_checks 115 stepData115 recoveryData115 rowData115
    transitionCode transition_checks recovery_check_115 row_check_115 move_target_115

private theorem recovery_check_116 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 116 recoveryData116 j = true := by
  have hg : seedIndices 116 = [27, 65, 139, 290, 1026] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_116 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 116 recoveryData116 rowData116 b j = true := by
  have hi : seedTransversalPattern 116 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData116 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData116 (rowMember rowData116 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData116 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_116 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData116 j b = rowTarget rowData116 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound116 : MoveSound 116 stepData116 :=
  moveSound_of_checks 116 stepData116 recoveryData116 rowData116
    transitionCode transition_checks recovery_check_116 row_check_116 move_target_116

private theorem recovery_check_117 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 117 recoveryData117 j = true := by
  have hg : seedIndices 117 = [27, 65, 139, 297, 1024] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_117 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 117 recoveryData117 rowData117 b j = true := by
  have hi : seedTransversalPattern 117 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData117 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData117 (rowMember rowData117 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData117 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_117 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData117 j b = rowTarget rowData117 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound117 : MoveSound 117 stepData117 :=
  moveSound_of_checks 117 stepData117 recoveryData117 rowData117
    transitionCode transition_checks recovery_check_117 row_check_117 move_target_117

private theorem recovery_check_118 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 118 recoveryData118 j = true := by
  have hg : seedIndices 118 = [27, 65, 139, 297, 1033] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_118 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 118 recoveryData118 rowData118 b j = true := by
  have hi : seedTransversalPattern 118 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData118 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData118 (rowMember rowData118 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData118 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_118 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData118 j b = rowTarget rowData118 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound118 : MoveSound 118 stepData118 :=
  moveSound_of_checks 118 stepData118 recoveryData118 rowData118
    transitionCode transition_checks recovery_check_118 row_check_118 move_target_118

private theorem recovery_check_119 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 119 recoveryData119 j = true := by
  have hg : seedIndices 119 = [27, 65, 139, 297, 1035] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_119 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 119 recoveryData119 rowData119 b j = true := by
  have hi : seedTransversalPattern 119 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData119 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData119 (rowMember rowData119 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData119 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_119 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData119 j b = rowTarget rowData119 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound119 : MoveSound 119 stepData119 :=
  moveSound_of_checks 119 stepData119 recoveryData119 rowData119
    transitionCode transition_checks recovery_check_119 row_check_119 move_target_119

private theorem recovery_check_120 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 120 recoveryData120 j = true := by
  have hg : seedIndices 120 = [27, 65, 139, 299, 1026] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_120 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 120 recoveryData120 rowData120 b j = true := by
  have hi : seedTransversalPattern 120 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData120 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData120 (rowMember rowData120 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData120 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_120 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData120 j b = rowTarget rowData120 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound120 : MoveSound 120 stepData120 :=
  moveSound_of_checks 120 stepData120 recoveryData120 rowData120
    transitionCode transition_checks recovery_check_120 row_check_120 move_target_120

private theorem recovery_check_121 : ∀ j : Fin 64,
    SylowFactorizationCertificate.recoveryTest 121 recoveryData121 j = true := by
  have hg : seedIndices 121 = [27, 65, 139, 299, 1033] := by decide +kernel
  simp only [SylowFactorizationCertificate.recoveryTest, hg]
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem row_check_121 : ∀ (b : Fin 32) (j : Fin 8),
    rowTest transitionCode 121 recoveryData121 rowData121 b j = true := by
  have hi : seedTransversalPattern 121 = 22 := by decide +kernel
  simp only [rowTest, hi]
  change ∀ (b : Fin 32) (j : Fin 8),
    (let c := transitionCode (rowEquation rowData121 b j)
     (transitionT c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] b) &&
     (transitionG c == j) &&
     (transitionQ c == recoveryQ recoveryData121 (rowMember rowData121 b j)) &&
     (transitionU c == ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] (rowTarget rowData121 b j))) = true
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

private theorem move_target_121 : ∀ (b : Fin 32) (j : Fin 8),
    move stepData121 j b = rowTarget rowData121 b j := by
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel

theorem moveSound121 : MoveSound 121 stepData121 :=
  moveSound_of_checks 121 stepData121 recoveryData121 rowData121
    transitionCode transition_checks recovery_check_121 row_check_121 move_target_121


end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
