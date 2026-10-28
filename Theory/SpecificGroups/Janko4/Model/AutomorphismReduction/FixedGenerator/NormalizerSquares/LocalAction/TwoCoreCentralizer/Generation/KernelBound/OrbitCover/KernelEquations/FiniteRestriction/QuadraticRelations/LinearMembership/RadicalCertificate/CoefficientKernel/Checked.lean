module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CoefficientKernel.Reduction

/-!
# Kernel-checked coefficient recovery rows

Each bounded batch checks both the packed product D T and the packed formula
1 + K F against the published remainder rows. All 1221 rows are covered;
no assertion from the witness generator is used as a proof.

Batches of 32 rows bound the memory of kernel reduction. The numerical source
is ../source/generate_completeness.py; see ../source/README.md.
-/

public section
-- Each batch releases its kernel-reduction state before the next begins.
set_option Elab.async false
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate.CoefficientKernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked00 : ∀ i : Fin 32,
    RowChecks ⟨0 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked01 : ∀ i : Fin 32,
    RowChecks ⟨32 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked02 : ∀ i : Fin 32,
    RowChecks ⟨64 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked03 : ∀ i : Fin 32,
    RowChecks ⟨96 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked04 : ∀ i : Fin 32,
    RowChecks ⟨128 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked05 : ∀ i : Fin 32,
    RowChecks ⟨160 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked06 : ∀ i : Fin 32,
    RowChecks ⟨192 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked07 : ∀ i : Fin 32,
    RowChecks ⟨224 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked08 : ∀ i : Fin 32,
    RowChecks ⟨256 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked09 : ∀ i : Fin 32,
    RowChecks ⟨288 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked10 : ∀ i : Fin 32,
    RowChecks ⟨320 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked11 : ∀ i : Fin 32,
    RowChecks ⟨352 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked12 : ∀ i : Fin 32,
    RowChecks ⟨384 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked13 : ∀ i : Fin 32,
    RowChecks ⟨416 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked14 : ∀ i : Fin 32,
    RowChecks ⟨448 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked15 : ∀ i : Fin 32,
    RowChecks ⟨480 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked16 : ∀ i : Fin 32,
    RowChecks ⟨512 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked17 : ∀ i : Fin 32,
    RowChecks ⟨544 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked18 : ∀ i : Fin 32,
    RowChecks ⟨576 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked19 : ∀ i : Fin 32,
    RowChecks ⟨608 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked20 : ∀ i : Fin 32,
    RowChecks ⟨640 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked21 : ∀ i : Fin 32,
    RowChecks ⟨672 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked22 : ∀ i : Fin 32,
    RowChecks ⟨704 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked23 : ∀ i : Fin 32,
    RowChecks ⟨736 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked24 : ∀ i : Fin 32,
    RowChecks ⟨768 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked25 : ∀ i : Fin 32,
    RowChecks ⟨800 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked26 : ∀ i : Fin 32,
    RowChecks ⟨832 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked27 : ∀ i : Fin 32,
    RowChecks ⟨864 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked28 : ∀ i : Fin 32,
    RowChecks ⟨896 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked29 : ∀ i : Fin 32,
    RowChecks ⟨928 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked30 : ∀ i : Fin 32,
    RowChecks ⟨960 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked31 : ∀ i : Fin 32,
    RowChecks ⟨992 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked32 : ∀ i : Fin 32,
    RowChecks ⟨1024 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked33 : ∀ i : Fin 32,
    RowChecks ⟨1056 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked34 : ∀ i : Fin 32,
    RowChecks ⟨1088 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked35 : ∀ i : Fin 32,
    RowChecks ⟨1120 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked36 : ∀ i : Fin 32,
    RowChecks ⟨1152 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked37 : ∀ i : Fin 32,
    RowChecks ⟨1184 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checkedTail : ∀ i : Fin 5,
    RowChecks ⟨1216 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxRecDepth 10000 in
/-- All published recovery rows and remainder formulas pass kernel reduction. -/
theorem allRowChecks (i : Fin 1221) : RowChecks i := by
  by_cases hi : i.val < 1216
  · have h : ∀ b : Fin 38, ∀ j : Fin 32,
        RowChecks ⟨32 * b.val + j.val, by omega⟩ := by
      intro b
      fin_cases b
      · exact checked00
      · exact checked01
      · exact checked02
      · exact checked03
      · exact checked04
      · exact checked05
      · exact checked06
      · exact checked07
      · exact checked08
      · exact checked09
      · exact checked10
      · exact checked11
      · exact checked12
      · exact checked13
      · exact checked14
      · exact checked15
      · exact checked16
      · exact checked17
      · exact checked18
      · exact checked19
      · exact checked20
      · exact checked21
      · exact checked22
      · exact checked23
      · exact checked24
      · exact checked25
      · exact checked26
      · exact checked27
      · exact checked28
      · exact checked29
      · exact checked30
      · exact checked31
      · exact checked32
      · exact checked33
      · exact checked34
      · exact checked35
      · exact checked36
      · exact checked37
    have hb : i.val / 32 < 38 := by omega
    have hm : i.val % 32 < 32 := Nat.mod_lt _ (by decide)
    have hx := h ⟨i.val / 32, hb⟩ ⟨i.val % 32, hm⟩
    have heq : (⟨32 * (i.val / 32) + i.val % 32, by omega⟩ : Fin 1221) = i :=
      Fin.ext (Nat.div_add_mod i.val 32)
    exact heq ▸ hx
  · have hx := checkedTail ⟨i.val - 1216, by omega⟩
    have heq : (⟨1216 + (i.val - 1216), by omega⟩ : Fin 1221) = i :=
      Fin.ext (show 1216 + (i.val - 1216) = i.val by omega)
    exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate.CoefficientKernel
