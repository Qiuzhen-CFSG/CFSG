module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# Recovering every mask from its first row

Each row is below 2^112, so its binary matrix entries determine it.
The checked left inverse distinguishes all 8192 masks.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
private theorem recover_bound_0 : ∀ m : Fin 64,
    recover (row (0 + m.val)) = 0 + m.val ∧
      row (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_1 : ∀ m : Fin 64,
    recover (row (64 + m.val)) = 64 + m.val ∧
      row (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_2 : ∀ m : Fin 64,
    recover (row (128 + m.val)) = 128 + m.val ∧
      row (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_3 : ∀ m : Fin 64,
    recover (row (192 + m.val)) = 192 + m.val ∧
      row (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_4 : ∀ m : Fin 64,
    recover (row (256 + m.val)) = 256 + m.val ∧
      row (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_5 : ∀ m : Fin 64,
    recover (row (320 + m.val)) = 320 + m.val ∧
      row (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_6 : ∀ m : Fin 64,
    recover (row (384 + m.val)) = 384 + m.val ∧
      row (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_7 : ∀ m : Fin 64,
    recover (row (448 + m.val)) = 448 + m.val ∧
      row (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_8 : ∀ m : Fin 64,
    recover (row (512 + m.val)) = 512 + m.val ∧
      row (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_9 : ∀ m : Fin 64,
    recover (row (576 + m.val)) = 576 + m.val ∧
      row (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_10 : ∀ m : Fin 64,
    recover (row (640 + m.val)) = 640 + m.val ∧
      row (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_11 : ∀ m : Fin 64,
    recover (row (704 + m.val)) = 704 + m.val ∧
      row (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_12 : ∀ m : Fin 64,
    recover (row (768 + m.val)) = 768 + m.val ∧
      row (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_13 : ∀ m : Fin 64,
    recover (row (832 + m.val)) = 832 + m.val ∧
      row (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_14 : ∀ m : Fin 64,
    recover (row (896 + m.val)) = 896 + m.val ∧
      row (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_15 : ∀ m : Fin 64,
    recover (row (960 + m.val)) = 960 + m.val ∧
      row (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_16 : ∀ m : Fin 64,
    recover (row (1024 + m.val)) = 1024 + m.val ∧
      row (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_17 : ∀ m : Fin 64,
    recover (row (1088 + m.val)) = 1088 + m.val ∧
      row (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_18 : ∀ m : Fin 64,
    recover (row (1152 + m.val)) = 1152 + m.val ∧
      row (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_19 : ∀ m : Fin 64,
    recover (row (1216 + m.val)) = 1216 + m.val ∧
      row (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_20 : ∀ m : Fin 64,
    recover (row (1280 + m.val)) = 1280 + m.val ∧
      row (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_21 : ∀ m : Fin 64,
    recover (row (1344 + m.val)) = 1344 + m.val ∧
      row (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_22 : ∀ m : Fin 64,
    recover (row (1408 + m.val)) = 1408 + m.val ∧
      row (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_23 : ∀ m : Fin 64,
    recover (row (1472 + m.val)) = 1472 + m.val ∧
      row (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_24 : ∀ m : Fin 64,
    recover (row (1536 + m.val)) = 1536 + m.val ∧
      row (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_25 : ∀ m : Fin 64,
    recover (row (1600 + m.val)) = 1600 + m.val ∧
      row (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_26 : ∀ m : Fin 64,
    recover (row (1664 + m.val)) = 1664 + m.val ∧
      row (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_27 : ∀ m : Fin 64,
    recover (row (1728 + m.val)) = 1728 + m.val ∧
      row (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_28 : ∀ m : Fin 64,
    recover (row (1792 + m.val)) = 1792 + m.val ∧
      row (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_29 : ∀ m : Fin 64,
    recover (row (1856 + m.val)) = 1856 + m.val ∧
      row (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_30 : ∀ m : Fin 64,
    recover (row (1920 + m.val)) = 1920 + m.val ∧
      row (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_31 : ∀ m : Fin 64,
    recover (row (1984 + m.val)) = 1984 + m.val ∧
      row (1984 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_32 : ∀ m : Fin 64,
    recover (row (2048 + m.val)) = 2048 + m.val ∧
      row (2048 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_33 : ∀ m : Fin 64,
    recover (row (2112 + m.val)) = 2112 + m.val ∧
      row (2112 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_34 : ∀ m : Fin 64,
    recover (row (2176 + m.val)) = 2176 + m.val ∧
      row (2176 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_35 : ∀ m : Fin 64,
    recover (row (2240 + m.val)) = 2240 + m.val ∧
      row (2240 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_36 : ∀ m : Fin 64,
    recover (row (2304 + m.val)) = 2304 + m.val ∧
      row (2304 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_37 : ∀ m : Fin 64,
    recover (row (2368 + m.val)) = 2368 + m.val ∧
      row (2368 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_38 : ∀ m : Fin 64,
    recover (row (2432 + m.val)) = 2432 + m.val ∧
      row (2432 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_39 : ∀ m : Fin 64,
    recover (row (2496 + m.val)) = 2496 + m.val ∧
      row (2496 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_40 : ∀ m : Fin 64,
    recover (row (2560 + m.val)) = 2560 + m.val ∧
      row (2560 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_41 : ∀ m : Fin 64,
    recover (row (2624 + m.val)) = 2624 + m.val ∧
      row (2624 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_42 : ∀ m : Fin 64,
    recover (row (2688 + m.val)) = 2688 + m.val ∧
      row (2688 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_43 : ∀ m : Fin 64,
    recover (row (2752 + m.val)) = 2752 + m.val ∧
      row (2752 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_44 : ∀ m : Fin 64,
    recover (row (2816 + m.val)) = 2816 + m.val ∧
      row (2816 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_45 : ∀ m : Fin 64,
    recover (row (2880 + m.val)) = 2880 + m.val ∧
      row (2880 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_46 : ∀ m : Fin 64,
    recover (row (2944 + m.val)) = 2944 + m.val ∧
      row (2944 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_47 : ∀ m : Fin 64,
    recover (row (3008 + m.val)) = 3008 + m.val ∧
      row (3008 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_48 : ∀ m : Fin 64,
    recover (row (3072 + m.val)) = 3072 + m.val ∧
      row (3072 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_49 : ∀ m : Fin 64,
    recover (row (3136 + m.val)) = 3136 + m.val ∧
      row (3136 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_50 : ∀ m : Fin 64,
    recover (row (3200 + m.val)) = 3200 + m.val ∧
      row (3200 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_51 : ∀ m : Fin 64,
    recover (row (3264 + m.val)) = 3264 + m.val ∧
      row (3264 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_52 : ∀ m : Fin 64,
    recover (row (3328 + m.val)) = 3328 + m.val ∧
      row (3328 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_53 : ∀ m : Fin 64,
    recover (row (3392 + m.val)) = 3392 + m.val ∧
      row (3392 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_54 : ∀ m : Fin 64,
    recover (row (3456 + m.val)) = 3456 + m.val ∧
      row (3456 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_55 : ∀ m : Fin 64,
    recover (row (3520 + m.val)) = 3520 + m.val ∧
      row (3520 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_56 : ∀ m : Fin 64,
    recover (row (3584 + m.val)) = 3584 + m.val ∧
      row (3584 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_57 : ∀ m : Fin 64,
    recover (row (3648 + m.val)) = 3648 + m.val ∧
      row (3648 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_58 : ∀ m : Fin 64,
    recover (row (3712 + m.val)) = 3712 + m.val ∧
      row (3712 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_59 : ∀ m : Fin 64,
    recover (row (3776 + m.val)) = 3776 + m.val ∧
      row (3776 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_60 : ∀ m : Fin 64,
    recover (row (3840 + m.val)) = 3840 + m.val ∧
      row (3840 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_61 : ∀ m : Fin 64,
    recover (row (3904 + m.val)) = 3904 + m.val ∧
      row (3904 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_62 : ∀ m : Fin 64,
    recover (row (3968 + m.val)) = 3968 + m.val ∧
      row (3968 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_63 : ∀ m : Fin 64,
    recover (row (4032 + m.val)) = 4032 + m.val ∧
      row (4032 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_64 : ∀ m : Fin 64,
    recover (row (4096 + m.val)) = 4096 + m.val ∧
      row (4096 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_65 : ∀ m : Fin 64,
    recover (row (4160 + m.val)) = 4160 + m.val ∧
      row (4160 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_66 : ∀ m : Fin 64,
    recover (row (4224 + m.val)) = 4224 + m.val ∧
      row (4224 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_67 : ∀ m : Fin 64,
    recover (row (4288 + m.val)) = 4288 + m.val ∧
      row (4288 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_68 : ∀ m : Fin 64,
    recover (row (4352 + m.val)) = 4352 + m.val ∧
      row (4352 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_69 : ∀ m : Fin 64,
    recover (row (4416 + m.val)) = 4416 + m.val ∧
      row (4416 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_70 : ∀ m : Fin 64,
    recover (row (4480 + m.val)) = 4480 + m.val ∧
      row (4480 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_71 : ∀ m : Fin 64,
    recover (row (4544 + m.val)) = 4544 + m.val ∧
      row (4544 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_72 : ∀ m : Fin 64,
    recover (row (4608 + m.val)) = 4608 + m.val ∧
      row (4608 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_73 : ∀ m : Fin 64,
    recover (row (4672 + m.val)) = 4672 + m.val ∧
      row (4672 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_74 : ∀ m : Fin 64,
    recover (row (4736 + m.val)) = 4736 + m.val ∧
      row (4736 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_75 : ∀ m : Fin 64,
    recover (row (4800 + m.val)) = 4800 + m.val ∧
      row (4800 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_76 : ∀ m : Fin 64,
    recover (row (4864 + m.val)) = 4864 + m.val ∧
      row (4864 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_77 : ∀ m : Fin 64,
    recover (row (4928 + m.val)) = 4928 + m.val ∧
      row (4928 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_78 : ∀ m : Fin 64,
    recover (row (4992 + m.val)) = 4992 + m.val ∧
      row (4992 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_79 : ∀ m : Fin 64,
    recover (row (5056 + m.val)) = 5056 + m.val ∧
      row (5056 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_80 : ∀ m : Fin 64,
    recover (row (5120 + m.val)) = 5120 + m.val ∧
      row (5120 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_81 : ∀ m : Fin 64,
    recover (row (5184 + m.val)) = 5184 + m.val ∧
      row (5184 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_82 : ∀ m : Fin 64,
    recover (row (5248 + m.val)) = 5248 + m.val ∧
      row (5248 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_83 : ∀ m : Fin 64,
    recover (row (5312 + m.val)) = 5312 + m.val ∧
      row (5312 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_84 : ∀ m : Fin 64,
    recover (row (5376 + m.val)) = 5376 + m.val ∧
      row (5376 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_85 : ∀ m : Fin 64,
    recover (row (5440 + m.val)) = 5440 + m.val ∧
      row (5440 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_86 : ∀ m : Fin 64,
    recover (row (5504 + m.val)) = 5504 + m.val ∧
      row (5504 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_87 : ∀ m : Fin 64,
    recover (row (5568 + m.val)) = 5568 + m.val ∧
      row (5568 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_88 : ∀ m : Fin 64,
    recover (row (5632 + m.val)) = 5632 + m.val ∧
      row (5632 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_89 : ∀ m : Fin 64,
    recover (row (5696 + m.val)) = 5696 + m.val ∧
      row (5696 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_90 : ∀ m : Fin 64,
    recover (row (5760 + m.val)) = 5760 + m.val ∧
      row (5760 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_91 : ∀ m : Fin 64,
    recover (row (5824 + m.val)) = 5824 + m.val ∧
      row (5824 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_92 : ∀ m : Fin 64,
    recover (row (5888 + m.val)) = 5888 + m.val ∧
      row (5888 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_93 : ∀ m : Fin 64,
    recover (row (5952 + m.val)) = 5952 + m.val ∧
      row (5952 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_94 : ∀ m : Fin 64,
    recover (row (6016 + m.val)) = 6016 + m.val ∧
      row (6016 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_95 : ∀ m : Fin 64,
    recover (row (6080 + m.val)) = 6080 + m.val ∧
      row (6080 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_96 : ∀ m : Fin 64,
    recover (row (6144 + m.val)) = 6144 + m.val ∧
      row (6144 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_97 : ∀ m : Fin 64,
    recover (row (6208 + m.val)) = 6208 + m.val ∧
      row (6208 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_98 : ∀ m : Fin 64,
    recover (row (6272 + m.val)) = 6272 + m.val ∧
      row (6272 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_99 : ∀ m : Fin 64,
    recover (row (6336 + m.val)) = 6336 + m.val ∧
      row (6336 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_100 : ∀ m : Fin 64,
    recover (row (6400 + m.val)) = 6400 + m.val ∧
      row (6400 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_101 : ∀ m : Fin 64,
    recover (row (6464 + m.val)) = 6464 + m.val ∧
      row (6464 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_102 : ∀ m : Fin 64,
    recover (row (6528 + m.val)) = 6528 + m.val ∧
      row (6528 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_103 : ∀ m : Fin 64,
    recover (row (6592 + m.val)) = 6592 + m.val ∧
      row (6592 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_104 : ∀ m : Fin 64,
    recover (row (6656 + m.val)) = 6656 + m.val ∧
      row (6656 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_105 : ∀ m : Fin 64,
    recover (row (6720 + m.val)) = 6720 + m.val ∧
      row (6720 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_106 : ∀ m : Fin 64,
    recover (row (6784 + m.val)) = 6784 + m.val ∧
      row (6784 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_107 : ∀ m : Fin 64,
    recover (row (6848 + m.val)) = 6848 + m.val ∧
      row (6848 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_108 : ∀ m : Fin 64,
    recover (row (6912 + m.val)) = 6912 + m.val ∧
      row (6912 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_109 : ∀ m : Fin 64,
    recover (row (6976 + m.val)) = 6976 + m.val ∧
      row (6976 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_110 : ∀ m : Fin 64,
    recover (row (7040 + m.val)) = 7040 + m.val ∧
      row (7040 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_111 : ∀ m : Fin 64,
    recover (row (7104 + m.val)) = 7104 + m.val ∧
      row (7104 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_112 : ∀ m : Fin 64,
    recover (row (7168 + m.val)) = 7168 + m.val ∧
      row (7168 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_113 : ∀ m : Fin 64,
    recover (row (7232 + m.val)) = 7232 + m.val ∧
      row (7232 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_114 : ∀ m : Fin 64,
    recover (row (7296 + m.val)) = 7296 + m.val ∧
      row (7296 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_115 : ∀ m : Fin 64,
    recover (row (7360 + m.val)) = 7360 + m.val ∧
      row (7360 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_116 : ∀ m : Fin 64,
    recover (row (7424 + m.val)) = 7424 + m.val ∧
      row (7424 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_117 : ∀ m : Fin 64,
    recover (row (7488 + m.val)) = 7488 + m.val ∧
      row (7488 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_118 : ∀ m : Fin 64,
    recover (row (7552 + m.val)) = 7552 + m.val ∧
      row (7552 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_119 : ∀ m : Fin 64,
    recover (row (7616 + m.val)) = 7616 + m.val ∧
      row (7616 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_120 : ∀ m : Fin 64,
    recover (row (7680 + m.val)) = 7680 + m.val ∧
      row (7680 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_121 : ∀ m : Fin 64,
    recover (row (7744 + m.val)) = 7744 + m.val ∧
      row (7744 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_122 : ∀ m : Fin 64,
    recover (row (7808 + m.val)) = 7808 + m.val ∧
      row (7808 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_123 : ∀ m : Fin 64,
    recover (row (7872 + m.val)) = 7872 + m.val ∧
      row (7872 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_124 : ∀ m : Fin 64,
    recover (row (7936 + m.val)) = 7936 + m.val ∧
      row (7936 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_125 : ∀ m : Fin 64,
    recover (row (8000 + m.val)) = 8000 + m.val ∧
      row (8000 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_126 : ∀ m : Fin 64,
    recover (row (8064 + m.val)) = 8064 + m.val ∧
      row (8064 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem recover_bound_127 : ∀ m : Fin 64,
    recover (row (8128 + m.val)) = 8128 + m.val ∧
      row (8128 + m.val) < 2^112 := by
  decide +kernel

theorem recover_bound (m : Fin 8192) :
    recover (row m.val) = m.val ∧ row m.val < 2^112 := by
  apply check_blocks (P := fun k => recover (row k) = k ∧ row k < 2^112)
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact recover_bound_0
  · exact recover_bound_1
  · exact recover_bound_2
  · exact recover_bound_3
  · exact recover_bound_4
  · exact recover_bound_5
  · exact recover_bound_6
  · exact recover_bound_7
  · exact recover_bound_8
  · exact recover_bound_9
  · exact recover_bound_10
  · exact recover_bound_11
  · exact recover_bound_12
  · exact recover_bound_13
  · exact recover_bound_14
  · exact recover_bound_15
  · exact recover_bound_16
  · exact recover_bound_17
  · exact recover_bound_18
  · exact recover_bound_19
  · exact recover_bound_20
  · exact recover_bound_21
  · exact recover_bound_22
  · exact recover_bound_23
  · exact recover_bound_24
  · exact recover_bound_25
  · exact recover_bound_26
  · exact recover_bound_27
  · exact recover_bound_28
  · exact recover_bound_29
  · exact recover_bound_30
  · exact recover_bound_31
  · exact recover_bound_32
  · exact recover_bound_33
  · exact recover_bound_34
  · exact recover_bound_35
  · exact recover_bound_36
  · exact recover_bound_37
  · exact recover_bound_38
  · exact recover_bound_39
  · exact recover_bound_40
  · exact recover_bound_41
  · exact recover_bound_42
  · exact recover_bound_43
  · exact recover_bound_44
  · exact recover_bound_45
  · exact recover_bound_46
  · exact recover_bound_47
  · exact recover_bound_48
  · exact recover_bound_49
  · exact recover_bound_50
  · exact recover_bound_51
  · exact recover_bound_52
  · exact recover_bound_53
  · exact recover_bound_54
  · exact recover_bound_55
  · exact recover_bound_56
  · exact recover_bound_57
  · exact recover_bound_58
  · exact recover_bound_59
  · exact recover_bound_60
  · exact recover_bound_61
  · exact recover_bound_62
  · exact recover_bound_63
  · exact recover_bound_64
  · exact recover_bound_65
  · exact recover_bound_66
  · exact recover_bound_67
  · exact recover_bound_68
  · exact recover_bound_69
  · exact recover_bound_70
  · exact recover_bound_71
  · exact recover_bound_72
  · exact recover_bound_73
  · exact recover_bound_74
  · exact recover_bound_75
  · exact recover_bound_76
  · exact recover_bound_77
  · exact recover_bound_78
  · exact recover_bound_79
  · exact recover_bound_80
  · exact recover_bound_81
  · exact recover_bound_82
  · exact recover_bound_83
  · exact recover_bound_84
  · exact recover_bound_85
  · exact recover_bound_86
  · exact recover_bound_87
  · exact recover_bound_88
  · exact recover_bound_89
  · exact recover_bound_90
  · exact recover_bound_91
  · exact recover_bound_92
  · exact recover_bound_93
  · exact recover_bound_94
  · exact recover_bound_95
  · exact recover_bound_96
  · exact recover_bound_97
  · exact recover_bound_98
  · exact recover_bound_99
  · exact recover_bound_100
  · exact recover_bound_101
  · exact recover_bound_102
  · exact recover_bound_103
  · exact recover_bound_104
  · exact recover_bound_105
  · exact recover_bound_106
  · exact recover_bound_107
  · exact recover_bound_108
  · exact recover_bound_109
  · exact recover_bound_110
  · exact recover_bound_111
  · exact recover_bound_112
  · exact recover_bound_113
  · exact recover_bound_114
  · exact recover_bound_115
  · exact recover_bound_116
  · exact recover_bound_117
  · exact recover_bound_118
  · exact recover_bound_119
  · exact recover_bound_120
  · exact recover_bound_121
  · exact recover_bound_122
  · exact recover_bound_123
  · exact recover_bound_124
  · exact recover_bound_125
  · exact recover_bound_126
  · exact recover_bound_127

theorem row_zero : row 0 = 1 := by decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
