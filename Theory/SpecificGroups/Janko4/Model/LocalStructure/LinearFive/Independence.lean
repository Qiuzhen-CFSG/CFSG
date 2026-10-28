module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.FirstRow

/-!
# Checked independence of the native linear-five matrices

Blocks of at most 64 rows certify all 1023 recurrence steps. A checked inverse
table recovers every mask. Thus all 1024 binary products of the ten actual
candidate matrices are distinct, independently of their group relations.
-/

public section
namespace Janko4.LocalStructure.LinearFive.NativeIndependence
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
private theorem check_blocks {P : ℕ → Prop} {size blocks : ℕ} (hs : 0 < size)
    (h : ∀ b : Fin blocks, ∀ i : Fin size, P (size * b.val + i.val))
    (m : Fin (size * blocks)) : P m.val := by
  have hb : m.val / size < blocks := (Nat.div_lt_iff_lt_mul hs).2
    (by simpa only [Nat.mul_comm] using m.isLt)
  simpa only [Nat.div_add_mod] using
    h ⟨m.val / size, hb⟩ ⟨m.val % size, Nat.mod_lt _ hs⟩
set_option maxHeartbeats 800000 in
private theorem step0_0 : ∀ m : Fin 1,
    row ((0 + m.val) + 1) = packedRow (row (0 + m.val)) (generatorRows 0) := by
  decide +kernel
private theorem step0 (m : Fin 1) :
    row (m.val + 1) = packedRow (row m.val) (generatorRows 0) := by
  simpa only [Nat.zero_add] using step0_0 m
set_option maxHeartbeats 800000 in
private theorem step1_0 : ∀ m : Fin 2,
    row ((0 + m.val) + 2) = packedRow (row (0 + m.val)) (generatorRows 1) := by
  decide +kernel
private theorem step1 (m : Fin 2) :
    row (m.val + 2) = packedRow (row m.val) (generatorRows 1) := by
  simpa only [Nat.zero_add] using step1_0 m
set_option maxHeartbeats 800000 in
private theorem step2_0 : ∀ m : Fin 4,
    row ((0 + m.val) + 4) = packedRow (row (0 + m.val)) (generatorRows 2) := by
  decide +kernel
private theorem step2 (m : Fin 4) :
    row (m.val + 4) = packedRow (row m.val) (generatorRows 2) := by
  simpa only [Nat.zero_add] using step2_0 m
set_option maxHeartbeats 800000 in
private theorem step3_0 : ∀ m : Fin 8,
    row ((0 + m.val) + 8) = packedRow (row (0 + m.val)) (generatorRows 3) := by
  decide +kernel
private theorem step3 (m : Fin 8) :
    row (m.val + 8) = packedRow (row m.val) (generatorRows 3) := by
  simpa only [Nat.zero_add] using step3_0 m
set_option maxHeartbeats 800000 in
private theorem step4_0 : ∀ m : Fin 16,
    row ((0 + m.val) + 16) = packedRow (row (0 + m.val)) (generatorRows 4) := by
  decide +kernel
private theorem step4 (m : Fin 16) :
    row (m.val + 16) = packedRow (row m.val) (generatorRows 4) := by
  simpa only [Nat.zero_add] using step4_0 m
set_option maxHeartbeats 800000 in
private theorem step5_0 : ∀ m : Fin 32,
    row ((0 + m.val) + 32) = packedRow (row (0 + m.val)) (generatorRows 5) := by
  decide +kernel
private theorem step5 (m : Fin 32) :
    row (m.val + 32) = packedRow (row m.val) (generatorRows 5) := by
  simpa only [Nat.zero_add] using step5_0 m
set_option maxHeartbeats 800000 in
private theorem step6_0 : ∀ m : Fin 64,
    row ((0 + m.val) + 64) = packedRow (row (0 + m.val)) (generatorRows 6) := by
  decide +kernel
private theorem step6 (m : Fin 64) :
    row (m.val + 64) = packedRow (row m.val) (generatorRows 6) := by
  simpa only [Nat.zero_add] using step6_0 m
set_option maxHeartbeats 800000 in
private theorem step7_0 : ∀ m : Fin 64,
    row ((0 + m.val) + 128) = packedRow (row (0 + m.val)) (generatorRows 7) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step7_1 : ∀ m : Fin 64,
    row ((64 + m.val) + 128) = packedRow (row (64 + m.val)) (generatorRows 7) := by
  decide +kernel
private theorem step7 (m : Fin 128) :
    row (m.val + 128) = packedRow (row m.val) (generatorRows 7) := by
  apply check_blocks (P := fun k => row (k + 128) = packedRow (row k) (generatorRows 7))
    (size := 64) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step7_0
  · exact step7_1
set_option maxHeartbeats 800000 in
private theorem step8_0 : ∀ m : Fin 64,
    row ((0 + m.val) + 256) = packedRow (row (0 + m.val)) (generatorRows 8) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step8_1 : ∀ m : Fin 64,
    row ((64 + m.val) + 256) = packedRow (row (64 + m.val)) (generatorRows 8) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step8_2 : ∀ m : Fin 64,
    row ((128 + m.val) + 256) = packedRow (row (128 + m.val)) (generatorRows 8) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step8_3 : ∀ m : Fin 64,
    row ((192 + m.val) + 256) = packedRow (row (192 + m.val)) (generatorRows 8) := by
  decide +kernel
private theorem step8 (m : Fin 256) :
    row (m.val + 256) = packedRow (row m.val) (generatorRows 8) := by
  apply check_blocks (P := fun k => row (k + 256) = packedRow (row k) (generatorRows 8))
    (size := 64) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step8_0
  · exact step8_1
  · exact step8_2
  · exact step8_3
set_option maxHeartbeats 800000 in
private theorem step9_0 : ∀ m : Fin 64,
    row ((0 + m.val) + 512) = packedRow (row (0 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_1 : ∀ m : Fin 64,
    row ((64 + m.val) + 512) = packedRow (row (64 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_2 : ∀ m : Fin 64,
    row ((128 + m.val) + 512) = packedRow (row (128 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_3 : ∀ m : Fin 64,
    row ((192 + m.val) + 512) = packedRow (row (192 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_4 : ∀ m : Fin 64,
    row ((256 + m.val) + 512) = packedRow (row (256 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_5 : ∀ m : Fin 64,
    row ((320 + m.val) + 512) = packedRow (row (320 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_6 : ∀ m : Fin 64,
    row ((384 + m.val) + 512) = packedRow (row (384 + m.val)) (generatorRows 9) := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem step9_7 : ∀ m : Fin 64,
    row ((448 + m.val) + 512) = packedRow (row (448 + m.val)) (generatorRows 9) := by
  decide +kernel
private theorem step9 (m : Fin 512) :
    row (m.val + 512) = packedRow (row m.val) (generatorRows 9) := by
  apply check_blocks (P := fun k => row (k + 512) = packedRow (row k) (generatorRows 9))
    (size := 64) (blocks := 8) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step9_0
  · exact step9_1
  · exact step9_2
  · exact step9_3
  · exact step9_4
  · exact step9_5
  · exact step9_6
  · exact step9_7
private theorem row_step (n : Fin 10) (m : Fin (2^n.val)) :
    row (m.val + 2^n.val) = packedRow (row m.val) (generatorRows n) := by
  fin_cases n
  · exact step0 m
  · exact step1 m
  · exact step2 m
  · exact step3 m
  · exact step4 m
  · exact step5 m
  · exact step6 m
  · exact step7 m
  · exact step8 m
  · exact step9 m
set_option maxHeartbeats 800000 in
private theorem recover_row : ∀ m : Fin 1024, recover (row m.val) = m.val := by
  decide +kernel
set_option maxHeartbeats 800000 in
private theorem row_bound : ∀ m : Fin 1024, row m.val < 2^112 := by
  decide +kernel

theorem matrixProduct_injective : Function.Injective matrixProduct :=
  matrixProduct_injective_of_certificate row (by decide +kernel) row_step
    recover recover_row row_bound

end Janko4.LocalStructure.LinearFive.NativeIndependence
