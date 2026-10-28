module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity.Rows
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity.Packed
public import Mathlib.Tactic.FinCases

/-!
# Kernel-checked first-row certificates

The eleven update blocks certify all 2047 nonempty masks. A bounded binary
search recovers each of the 2048 masks from its row. Every finite check uses
kernel reduction; blocks of at most 64 cases limit checking memory.
See `Rows` and `KernelCount.Tables` for the witness convention and ATLAS source.
-/

public section
namespace Janko4.Cardinality.KernelCount.Injectivity
open Janko4.GeneratorCertificates

private theorem check_blocks {P : ℕ → Prop} {size blocks : ℕ} (hs : 0 < size)
    (h : ∀ b : Fin blocks, ∀ i : Fin size, P (size * b.val + i.val))
    (m : Fin (size * blocks)) : P m.val := by
  have hb : m.val / size < blocks := (Nat.div_lt_iff_lt_mul hs).2
    (by simpa only [Nat.mul_comm] using m.isLt)
  simpa only [Nat.div_add_mod] using
    h ⟨m.val / size, hb⟩ ⟨m.val % size, Nat.mod_lt _ hs⟩

set_option maxRecDepth 10000 in
private theorem fast_step0 : ∀ m : Fin 1, row (m.val + 1) = fastPackedRow (row m.val) 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step1 : ∀ m : Fin 2, row (m.val + 2) = fastPackedRow (row m.val) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step2 : ∀ m : Fin 4, row (m.val + 4) = fastPackedRow (row m.val) 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step3 : ∀ m : Fin 8, row (m.val + 8) = fastPackedRow (row m.val) 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step4 : ∀ m : Fin 16, row (m.val + 16) = fastPackedRow (row m.val) 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step5 : ∀ m : Fin 32, row (m.val + 32) = fastPackedRow (row m.val) 5 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step6 : ∀ m : Fin 64, row (m.val + 64) = fastPackedRow (row m.val) 6 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step7_0 : ∀ m : Fin 64, row ((0 + m.val) + 128) = fastPackedRow (row (0 + m.val)) 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step7_1 : ∀ m : Fin 64, row ((64 + m.val) + 128) = fastPackedRow (row (64 + m.val)) 7 := by
  decide +kernel

private theorem fast_step7 (m : Fin 128) : row (m.val + 128) = fastPackedRow (row m.val) 7 := by
  apply check_blocks (P := fun k => row (k + 128) = fastPackedRow (row k) 7)
    (size := 64) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact fast_step7_0
  · exact fast_step7_1

set_option maxRecDepth 10000 in
private theorem fast_step8_0 : ∀ m : Fin 64, row ((0 + m.val) + 256) = fastPackedRow (row (0 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step8_1 : ∀ m : Fin 64, row ((64 + m.val) + 256) = fastPackedRow (row (64 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step8_2 : ∀ m : Fin 64, row ((128 + m.val) + 256) = fastPackedRow (row (128 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step8_3 : ∀ m : Fin 64, row ((192 + m.val) + 256) = fastPackedRow (row (192 + m.val)) 8 := by
  decide +kernel

private theorem fast_step8 (m : Fin 256) : row (m.val + 256) = fastPackedRow (row m.val) 8 := by
  apply check_blocks (P := fun k => row (k + 256) = fastPackedRow (row k) 8)
    (size := 64) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact fast_step8_0
  · exact fast_step8_1
  · exact fast_step8_2
  · exact fast_step8_3

set_option maxRecDepth 10000 in
private theorem fast_step9_0 : ∀ m : Fin 64, row ((0 + m.val) + 512) = fastPackedRow (row (0 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_1 : ∀ m : Fin 64, row ((64 + m.val) + 512) = fastPackedRow (row (64 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_2 : ∀ m : Fin 64, row ((128 + m.val) + 512) = fastPackedRow (row (128 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_3 : ∀ m : Fin 64, row ((192 + m.val) + 512) = fastPackedRow (row (192 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_4 : ∀ m : Fin 64, row ((256 + m.val) + 512) = fastPackedRow (row (256 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_5 : ∀ m : Fin 64, row ((320 + m.val) + 512) = fastPackedRow (row (320 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_6 : ∀ m : Fin 64, row ((384 + m.val) + 512) = fastPackedRow (row (384 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step9_7 : ∀ m : Fin 64, row ((448 + m.val) + 512) = fastPackedRow (row (448 + m.val)) 9 := by
  decide +kernel

private theorem fast_step9 (m : Fin 512) : row (m.val + 512) = fastPackedRow (row m.val) 9 := by
  apply check_blocks (P := fun k => row (k + 512) = fastPackedRow (row k) 9)
    (size := 64) (blocks := 8) (by decide) ?_ m
  intro b
  fin_cases b
  · exact fast_step9_0
  · exact fast_step9_1
  · exact fast_step9_2
  · exact fast_step9_3
  · exact fast_step9_4
  · exact fast_step9_5
  · exact fast_step9_6
  · exact fast_step9_7

set_option maxRecDepth 10000 in
private theorem fast_step10_0 : ∀ m : Fin 64, row ((0 + m.val) + 1024) = fastPackedRow (row (0 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_1 : ∀ m : Fin 64, row ((64 + m.val) + 1024) = fastPackedRow (row (64 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_2 : ∀ m : Fin 64, row ((128 + m.val) + 1024) = fastPackedRow (row (128 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_3 : ∀ m : Fin 64, row ((192 + m.val) + 1024) = fastPackedRow (row (192 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_4 : ∀ m : Fin 64, row ((256 + m.val) + 1024) = fastPackedRow (row (256 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_5 : ∀ m : Fin 64, row ((320 + m.val) + 1024) = fastPackedRow (row (320 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_6 : ∀ m : Fin 64, row ((384 + m.val) + 1024) = fastPackedRow (row (384 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_7 : ∀ m : Fin 64, row ((448 + m.val) + 1024) = fastPackedRow (row (448 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_8 : ∀ m : Fin 64, row ((512 + m.val) + 1024) = fastPackedRow (row (512 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_9 : ∀ m : Fin 64, row ((576 + m.val) + 1024) = fastPackedRow (row (576 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_10 : ∀ m : Fin 64, row ((640 + m.val) + 1024) = fastPackedRow (row (640 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_11 : ∀ m : Fin 64, row ((704 + m.val) + 1024) = fastPackedRow (row (704 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_12 : ∀ m : Fin 64, row ((768 + m.val) + 1024) = fastPackedRow (row (768 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_13 : ∀ m : Fin 64, row ((832 + m.val) + 1024) = fastPackedRow (row (832 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_14 : ∀ m : Fin 64, row ((896 + m.val) + 1024) = fastPackedRow (row (896 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fast_step10_15 : ∀ m : Fin 64, row ((960 + m.val) + 1024) = fastPackedRow (row (960 + m.val)) 10 := by
  decide +kernel

private theorem fast_step10 (m : Fin 1024) : row (m.val + 1024) = fastPackedRow (row m.val) 10 := by
  apply check_blocks (P := fun k => row (k + 1024) = fastPackedRow (row k) 10)
    (size := 64) (blocks := 16) (by decide) ?_ m
  intro b
  fin_cases b
  · exact fast_step10_0
  · exact fast_step10_1
  · exact fast_step10_2
  · exact fast_step10_3
  · exact fast_step10_4
  · exact fast_step10_5
  · exact fast_step10_6
  · exact fast_step10_7
  · exact fast_step10_8
  · exact fast_step10_9
  · exact fast_step10_10
  · exact fast_step10_11
  · exact fast_step10_12
  · exact fast_step10_13
  · exact fast_step10_14
  · exact fast_step10_15

theorem row_step (n : Fin 11) (m : Fin (2^n.val)) :
    row (m.val + 2^n.val) = packedRow (row m.val) (basisRows n) := by
  rw [← fastPackedRow_eq]
  fin_cases n
  · exact fast_step0 m
  · exact fast_step1 m
  · exact fast_step2 m
  · exact fast_step3 m
  · exact fast_step4 m
  · exact fast_step5 m
  · exact fast_step6 m
  · exact fast_step7 m
  · exact fast_step8 m
  · exact fast_step9 m
  · exact fast_step10 m

set_option maxRecDepth 10000 in
private theorem recover_row_0 : ∀ m : Fin 64, recover (row (0 + m.val)) = (0 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_1 : ∀ m : Fin 64, recover (row (64 + m.val)) = (64 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_2 : ∀ m : Fin 64, recover (row (128 + m.val)) = (128 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_3 : ∀ m : Fin 64, recover (row (192 + m.val)) = (192 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_4 : ∀ m : Fin 64, recover (row (256 + m.val)) = (256 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_5 : ∀ m : Fin 64, recover (row (320 + m.val)) = (320 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_6 : ∀ m : Fin 64, recover (row (384 + m.val)) = (384 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_7 : ∀ m : Fin 64, recover (row (448 + m.val)) = (448 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_8 : ∀ m : Fin 64, recover (row (512 + m.val)) = (512 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_9 : ∀ m : Fin 64, recover (row (576 + m.val)) = (576 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_10 : ∀ m : Fin 64, recover (row (640 + m.val)) = (640 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_11 : ∀ m : Fin 64, recover (row (704 + m.val)) = (704 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_12 : ∀ m : Fin 64, recover (row (768 + m.val)) = (768 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_13 : ∀ m : Fin 64, recover (row (832 + m.val)) = (832 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_14 : ∀ m : Fin 64, recover (row (896 + m.val)) = (896 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_15 : ∀ m : Fin 64, recover (row (960 + m.val)) = (960 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_16 : ∀ m : Fin 64, recover (row (1024 + m.val)) = (1024 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_17 : ∀ m : Fin 64, recover (row (1088 + m.val)) = (1088 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_18 : ∀ m : Fin 64, recover (row (1152 + m.val)) = (1152 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_19 : ∀ m : Fin 64, recover (row (1216 + m.val)) = (1216 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_20 : ∀ m : Fin 64, recover (row (1280 + m.val)) = (1280 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_21 : ∀ m : Fin 64, recover (row (1344 + m.val)) = (1344 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_22 : ∀ m : Fin 64, recover (row (1408 + m.val)) = (1408 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_23 : ∀ m : Fin 64, recover (row (1472 + m.val)) = (1472 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_24 : ∀ m : Fin 64, recover (row (1536 + m.val)) = (1536 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_25 : ∀ m : Fin 64, recover (row (1600 + m.val)) = (1600 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_26 : ∀ m : Fin 64, recover (row (1664 + m.val)) = (1664 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_27 : ∀ m : Fin 64, recover (row (1728 + m.val)) = (1728 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_28 : ∀ m : Fin 64, recover (row (1792 + m.val)) = (1792 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_29 : ∀ m : Fin 64, recover (row (1856 + m.val)) = (1856 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_30 : ∀ m : Fin 64, recover (row (1920 + m.val)) = (1920 + m.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_row_31 : ∀ m : Fin 64, recover (row (1984 + m.val)) = (1984 + m.val) := by
  decide +kernel

theorem recover_row (m : Fin 2048) : recover (row m.val) = m.val := by
  apply check_blocks (P := fun k => recover (row k) = k)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact recover_row_0
  · exact recover_row_1
  · exact recover_row_2
  · exact recover_row_3
  · exact recover_row_4
  · exact recover_row_5
  · exact recover_row_6
  · exact recover_row_7
  · exact recover_row_8
  · exact recover_row_9
  · exact recover_row_10
  · exact recover_row_11
  · exact recover_row_12
  · exact recover_row_13
  · exact recover_row_14
  · exact recover_row_15
  · exact recover_row_16
  · exact recover_row_17
  · exact recover_row_18
  · exact recover_row_19
  · exact recover_row_20
  · exact recover_row_21
  · exact recover_row_22
  · exact recover_row_23
  · exact recover_row_24
  · exact recover_row_25
  · exact recover_row_26
  · exact recover_row_27
  · exact recover_row_28
  · exact recover_row_29
  · exact recover_row_30
  · exact recover_row_31

set_option maxRecDepth 10000 in
private theorem row_lt_0 : ∀ m : Fin 64, row (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_1 : ∀ m : Fin 64, row (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_2 : ∀ m : Fin 64, row (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_3 : ∀ m : Fin 64, row (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_4 : ∀ m : Fin 64, row (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_5 : ∀ m : Fin 64, row (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_6 : ∀ m : Fin 64, row (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_7 : ∀ m : Fin 64, row (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_8 : ∀ m : Fin 64, row (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_9 : ∀ m : Fin 64, row (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_10 : ∀ m : Fin 64, row (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_11 : ∀ m : Fin 64, row (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_12 : ∀ m : Fin 64, row (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_13 : ∀ m : Fin 64, row (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_14 : ∀ m : Fin 64, row (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_15 : ∀ m : Fin 64, row (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_16 : ∀ m : Fin 64, row (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_17 : ∀ m : Fin 64, row (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_18 : ∀ m : Fin 64, row (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_19 : ∀ m : Fin 64, row (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_20 : ∀ m : Fin 64, row (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_21 : ∀ m : Fin 64, row (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_22 : ∀ m : Fin 64, row (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_23 : ∀ m : Fin 64, row (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_24 : ∀ m : Fin 64, row (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_25 : ∀ m : Fin 64, row (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_26 : ∀ m : Fin 64, row (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_27 : ∀ m : Fin 64, row (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_28 : ∀ m : Fin 64, row (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_29 : ∀ m : Fin 64, row (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_30 : ∀ m : Fin 64, row (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem row_lt_31 : ∀ m : Fin 64, row (1984 + m.val) < 2^112 := by
  decide +kernel

theorem row_lt (m : Fin 2048) : row m.val < 2^112 := by
  apply check_blocks (P := fun k => row k < 2^112)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact row_lt_0
  · exact row_lt_1
  · exact row_lt_2
  · exact row_lt_3
  · exact row_lt_4
  · exact row_lt_5
  · exact row_lt_6
  · exact row_lt_7
  · exact row_lt_8
  · exact row_lt_9
  · exact row_lt_10
  · exact row_lt_11
  · exact row_lt_12
  · exact row_lt_13
  · exact row_lt_14
  · exact row_lt_15
  · exact row_lt_16
  · exact row_lt_17
  · exact row_lt_18
  · exact row_lt_19
  · exact row_lt_20
  · exact row_lt_21
  · exact row_lt_22
  · exact row_lt_23
  · exact row_lt_24
  · exact row_lt_25
  · exact row_lt_26
  · exact row_lt_27
  · exact row_lt_28
  · exact row_lt_29
  · exact row_lt_30
  · exact row_lt_31

theorem row_zero : row 0 = 1 := by decide +kernel

end Janko4.Cardinality.KernelCount.Injectivity
