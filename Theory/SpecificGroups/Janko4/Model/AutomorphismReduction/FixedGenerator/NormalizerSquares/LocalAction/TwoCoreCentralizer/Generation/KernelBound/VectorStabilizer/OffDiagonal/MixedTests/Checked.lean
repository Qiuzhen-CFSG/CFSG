module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTests.Reduction

/-!
# Checked Gaussian residues and complete recovery

Every used residue is checked against the actual thirteen radical generators
and the actual mixed generators. The last identity in each row verifies a
left inverse for the entire simultaneous system. Kernel reduction is split
into bounded batches to release its temporary state between certificates.

See source/generate.py and VectorStabilizer/source/README.md.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate

set_option maxHeartbeats 5000000 in
theorem pivotChecks : PivotChecks := by
  unfold PivotChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked00 : ∀ i : Fin 25,
    RowChecks ⟨0 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked01 : ∀ i : Fin 25,
    RowChecks ⟨25 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked02 : ∀ i : Fin 25,
    RowChecks ⟨50 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked03 : ∀ i : Fin 25,
    RowChecks ⟨75 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked04 : ∀ i : Fin 25,
    RowChecks ⟨100 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked05 : ∀ i : Fin 25,
    RowChecks ⟨125 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked06 : ∀ i : Fin 25,
    RowChecks ⟨150 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked07 : ∀ i : Fin 25,
    RowChecks ⟨175 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked08 : ∀ i : Fin 25,
    RowChecks ⟨200 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked09 : ∀ i : Fin 25,
    RowChecks ⟨225 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked10 : ∀ i : Fin 25,
    RowChecks ⟨250 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked11 : ∀ i : Fin 25,
    RowChecks ⟨275 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked12 : ∀ i : Fin 25,
    RowChecks ⟨300 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked13 : ∀ i : Fin 25,
    RowChecks ⟨325 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked14 : ∀ i : Fin 25,
    RowChecks ⟨350 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked15 : ∀ i : Fin 25,
    RowChecks ⟨375 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked16 : ∀ i : Fin 25,
    RowChecks ⟨400 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked17 : ∀ i : Fin 25,
    RowChecks ⟨425 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked18 : ∀ i : Fin 25,
    RowChecks ⟨450 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked19 : ∀ i : Fin 25,
    RowChecks ⟨475 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked20 : ∀ i : Fin 25,
    RowChecks ⟨500 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked21 : ∀ i : Fin 25,
    RowChecks ⟨525 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked22 : ∀ i : Fin 25,
    RowChecks ⟨550 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem checked23 : ∀ i : Fin 25,
    RowChecks ⟨575 + i.val, by omega⟩ := by
  unfold RowChecks
  decide +kernel

/-- All 600 residue and recovery identities hold by ordinary kernel reduction. -/
theorem allRowChecks (i : Fin 600) : RowChecks i := by
  have h : ∀ b : Fin 24, ∀ j : Fin 25,
      RowChecks ⟨25 * b.val + j.val, by omega⟩ := by
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
  have hb : i.val / 25 < 24 := by omega
  have hm : i.val % 25 < 25 := Nat.mod_lt _ (by decide)
  have hx := h ⟨i.val / 25, hb⟩ ⟨i.val % 25, hm⟩
  have heq : (⟨25 * (i.val / 25) + i.val % 25, by omega⟩ : Fin 600) = i :=
    Fin.ext (Nat.div_add_mod i.val 25)
  exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTestCertificate
