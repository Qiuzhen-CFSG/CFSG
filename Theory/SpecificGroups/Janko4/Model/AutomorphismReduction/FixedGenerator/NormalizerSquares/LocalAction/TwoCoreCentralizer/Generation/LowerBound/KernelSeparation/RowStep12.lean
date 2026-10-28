module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 12

The update appends the highest selected factor on the right.
These are equalities of packed rows, checked in the kernel.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
private theorem step_0 : ∀ m : Fin 64,
    row (0 + m.val + 4096) = fastRow (row (0 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_1 : ∀ m : Fin 64,
    row (64 + m.val + 4096) = fastRow (row (64 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_2 : ∀ m : Fin 64,
    row (128 + m.val + 4096) = fastRow (row (128 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_3 : ∀ m : Fin 64,
    row (192 + m.val + 4096) = fastRow (row (192 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_4 : ∀ m : Fin 64,
    row (256 + m.val + 4096) = fastRow (row (256 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_5 : ∀ m : Fin 64,
    row (320 + m.val + 4096) = fastRow (row (320 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_6 : ∀ m : Fin 64,
    row (384 + m.val + 4096) = fastRow (row (384 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_7 : ∀ m : Fin 64,
    row (448 + m.val + 4096) = fastRow (row (448 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_8 : ∀ m : Fin 64,
    row (512 + m.val + 4096) = fastRow (row (512 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_9 : ∀ m : Fin 64,
    row (576 + m.val + 4096) = fastRow (row (576 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_10 : ∀ m : Fin 64,
    row (640 + m.val + 4096) = fastRow (row (640 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_11 : ∀ m : Fin 64,
    row (704 + m.val + 4096) = fastRow (row (704 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_12 : ∀ m : Fin 64,
    row (768 + m.val + 4096) = fastRow (row (768 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_13 : ∀ m : Fin 64,
    row (832 + m.val + 4096) = fastRow (row (832 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_14 : ∀ m : Fin 64,
    row (896 + m.val + 4096) = fastRow (row (896 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_15 : ∀ m : Fin 64,
    row (960 + m.val + 4096) = fastRow (row (960 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_16 : ∀ m : Fin 64,
    row (1024 + m.val + 4096) = fastRow (row (1024 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_17 : ∀ m : Fin 64,
    row (1088 + m.val + 4096) = fastRow (row (1088 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_18 : ∀ m : Fin 64,
    row (1152 + m.val + 4096) = fastRow (row (1152 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_19 : ∀ m : Fin 64,
    row (1216 + m.val + 4096) = fastRow (row (1216 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_20 : ∀ m : Fin 64,
    row (1280 + m.val + 4096) = fastRow (row (1280 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_21 : ∀ m : Fin 64,
    row (1344 + m.val + 4096) = fastRow (row (1344 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_22 : ∀ m : Fin 64,
    row (1408 + m.val + 4096) = fastRow (row (1408 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_23 : ∀ m : Fin 64,
    row (1472 + m.val + 4096) = fastRow (row (1472 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_24 : ∀ m : Fin 64,
    row (1536 + m.val + 4096) = fastRow (row (1536 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_25 : ∀ m : Fin 64,
    row (1600 + m.val + 4096) = fastRow (row (1600 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_26 : ∀ m : Fin 64,
    row (1664 + m.val + 4096) = fastRow (row (1664 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_27 : ∀ m : Fin 64,
    row (1728 + m.val + 4096) = fastRow (row (1728 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_28 : ∀ m : Fin 64,
    row (1792 + m.val + 4096) = fastRow (row (1792 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_29 : ∀ m : Fin 64,
    row (1856 + m.val + 4096) = fastRow (row (1856 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_30 : ∀ m : Fin 64,
    row (1920 + m.val + 4096) = fastRow (row (1920 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_31 : ∀ m : Fin 64,
    row (1984 + m.val + 4096) = fastRow (row (1984 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_32 : ∀ m : Fin 64,
    row (2048 + m.val + 4096) = fastRow (row (2048 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_33 : ∀ m : Fin 64,
    row (2112 + m.val + 4096) = fastRow (row (2112 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_34 : ∀ m : Fin 64,
    row (2176 + m.val + 4096) = fastRow (row (2176 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_35 : ∀ m : Fin 64,
    row (2240 + m.val + 4096) = fastRow (row (2240 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_36 : ∀ m : Fin 64,
    row (2304 + m.val + 4096) = fastRow (row (2304 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_37 : ∀ m : Fin 64,
    row (2368 + m.val + 4096) = fastRow (row (2368 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_38 : ∀ m : Fin 64,
    row (2432 + m.val + 4096) = fastRow (row (2432 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_39 : ∀ m : Fin 64,
    row (2496 + m.val + 4096) = fastRow (row (2496 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_40 : ∀ m : Fin 64,
    row (2560 + m.val + 4096) = fastRow (row (2560 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_41 : ∀ m : Fin 64,
    row (2624 + m.val + 4096) = fastRow (row (2624 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_42 : ∀ m : Fin 64,
    row (2688 + m.val + 4096) = fastRow (row (2688 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_43 : ∀ m : Fin 64,
    row (2752 + m.val + 4096) = fastRow (row (2752 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_44 : ∀ m : Fin 64,
    row (2816 + m.val + 4096) = fastRow (row (2816 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_45 : ∀ m : Fin 64,
    row (2880 + m.val + 4096) = fastRow (row (2880 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_46 : ∀ m : Fin 64,
    row (2944 + m.val + 4096) = fastRow (row (2944 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_47 : ∀ m : Fin 64,
    row (3008 + m.val + 4096) = fastRow (row (3008 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_48 : ∀ m : Fin 64,
    row (3072 + m.val + 4096) = fastRow (row (3072 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_49 : ∀ m : Fin 64,
    row (3136 + m.val + 4096) = fastRow (row (3136 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_50 : ∀ m : Fin 64,
    row (3200 + m.val + 4096) = fastRow (row (3200 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_51 : ∀ m : Fin 64,
    row (3264 + m.val + 4096) = fastRow (row (3264 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_52 : ∀ m : Fin 64,
    row (3328 + m.val + 4096) = fastRow (row (3328 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_53 : ∀ m : Fin 64,
    row (3392 + m.val + 4096) = fastRow (row (3392 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_54 : ∀ m : Fin 64,
    row (3456 + m.val + 4096) = fastRow (row (3456 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_55 : ∀ m : Fin 64,
    row (3520 + m.val + 4096) = fastRow (row (3520 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_56 : ∀ m : Fin 64,
    row (3584 + m.val + 4096) = fastRow (row (3584 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_57 : ∀ m : Fin 64,
    row (3648 + m.val + 4096) = fastRow (row (3648 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_58 : ∀ m : Fin 64,
    row (3712 + m.val + 4096) = fastRow (row (3712 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_59 : ∀ m : Fin 64,
    row (3776 + m.val + 4096) = fastRow (row (3776 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_60 : ∀ m : Fin 64,
    row (3840 + m.val + 4096) = fastRow (row (3840 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_61 : ∀ m : Fin 64,
    row (3904 + m.val + 4096) = fastRow (row (3904 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_62 : ∀ m : Fin 64,
    row (3968 + m.val + 4096) = fastRow (row (3968 + m.val)) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_63 : ∀ m : Fin 64,
    row (4032 + m.val + 4096) = fastRow (row (4032 + m.val)) 12 := by
  decide +kernel

theorem row_step_12 (m : Fin 4096) :
    row (m.val + 4096) = packedRow (row m.val) (factorRows 12) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 4096) = fastRow (row k) 12)
    (size := 64) (blocks := 64) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23
  · exact step_24
  · exact step_25
  · exact step_26
  · exact step_27
  · exact step_28
  · exact step_29
  · exact step_30
  · exact step_31
  · exact step_32
  · exact step_33
  · exact step_34
  · exact step_35
  · exact step_36
  · exact step_37
  · exact step_38
  · exact step_39
  · exact step_40
  · exact step_41
  · exact step_42
  · exact step_43
  · exact step_44
  · exact step_45
  · exact step_46
  · exact step_47
  · exact step_48
  · exact step_49
  · exact step_50
  · exact step_51
  · exact step_52
  · exact step_53
  · exact step_54
  · exact step_55
  · exact step_56
  · exact step_57
  · exact step_58
  · exact step_59
  · exact step_60
  · exact step_61
  · exact step_62
  · exact step_63

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
