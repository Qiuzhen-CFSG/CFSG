module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Witnesses

/-!
# Bounds and mask witnesses for fiber 1

Untrusted witnesses from the unchanged ATLAS J4G1-max2W1 data of
R. A. Wilson, S. J. Nickerson and J. N. Bray. All uses of these tables
require the kernel certificates. See `Coverage/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation

set_option maxRecDepth 10000 in
theorem backward_zero1 : backwardTable1 0 = liftEntry 1 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block0 : ∀ m : Fin 64,
    forwardTable1 (0 + m.val) < 2^112 ∧ backwardTable1 (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block1 : ∀ m : Fin 64,
    forwardTable1 (64 + m.val) < 2^112 ∧ backwardTable1 (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block2 : ∀ m : Fin 64,
    forwardTable1 (128 + m.val) < 2^112 ∧ backwardTable1 (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block3 : ∀ m : Fin 64,
    forwardTable1 (192 + m.val) < 2^112 ∧ backwardTable1 (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block4 : ∀ m : Fin 64,
    forwardTable1 (256 + m.val) < 2^112 ∧ backwardTable1 (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block5 : ∀ m : Fin 64,
    forwardTable1 (320 + m.val) < 2^112 ∧ backwardTable1 (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block6 : ∀ m : Fin 64,
    forwardTable1 (384 + m.val) < 2^112 ∧ backwardTable1 (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block7 : ∀ m : Fin 64,
    forwardTable1 (448 + m.val) < 2^112 ∧ backwardTable1 (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block8 : ∀ m : Fin 64,
    forwardTable1 (512 + m.val) < 2^112 ∧ backwardTable1 (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block9 : ∀ m : Fin 64,
    forwardTable1 (576 + m.val) < 2^112 ∧ backwardTable1 (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block10 : ∀ m : Fin 64,
    forwardTable1 (640 + m.val) < 2^112 ∧ backwardTable1 (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block11 : ∀ m : Fin 64,
    forwardTable1 (704 + m.val) < 2^112 ∧ backwardTable1 (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block12 : ∀ m : Fin 64,
    forwardTable1 (768 + m.val) < 2^112 ∧ backwardTable1 (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block13 : ∀ m : Fin 64,
    forwardTable1 (832 + m.val) < 2^112 ∧ backwardTable1 (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block14 : ∀ m : Fin 64,
    forwardTable1 (896 + m.val) < 2^112 ∧ backwardTable1 (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block15 : ∀ m : Fin 64,
    forwardTable1 (960 + m.val) < 2^112 ∧ backwardTable1 (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block16 : ∀ m : Fin 64,
    forwardTable1 (1024 + m.val) < 2^112 ∧ backwardTable1 (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block17 : ∀ m : Fin 64,
    forwardTable1 (1088 + m.val) < 2^112 ∧ backwardTable1 (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block18 : ∀ m : Fin 64,
    forwardTable1 (1152 + m.val) < 2^112 ∧ backwardTable1 (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block19 : ∀ m : Fin 64,
    forwardTable1 (1216 + m.val) < 2^112 ∧ backwardTable1 (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block20 : ∀ m : Fin 64,
    forwardTable1 (1280 + m.val) < 2^112 ∧ backwardTable1 (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block21 : ∀ m : Fin 64,
    forwardTable1 (1344 + m.val) < 2^112 ∧ backwardTable1 (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block22 : ∀ m : Fin 64,
    forwardTable1 (1408 + m.val) < 2^112 ∧ backwardTable1 (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block23 : ∀ m : Fin 64,
    forwardTable1 (1472 + m.val) < 2^112 ∧ backwardTable1 (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block24 : ∀ m : Fin 64,
    forwardTable1 (1536 + m.val) < 2^112 ∧ backwardTable1 (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block25 : ∀ m : Fin 64,
    forwardTable1 (1600 + m.val) < 2^112 ∧ backwardTable1 (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block26 : ∀ m : Fin 64,
    forwardTable1 (1664 + m.val) < 2^112 ∧ backwardTable1 (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block27 : ∀ m : Fin 64,
    forwardTable1 (1728 + m.val) < 2^112 ∧ backwardTable1 (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block28 : ∀ m : Fin 64,
    forwardTable1 (1792 + m.val) < 2^112 ∧ backwardTable1 (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block29 : ∀ m : Fin 64,
    forwardTable1 (1856 + m.val) < 2^112 ∧ backwardTable1 (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block30 : ∀ m : Fin 64,
    forwardTable1 (1920 + m.val) < 2^112 ∧ backwardTable1 (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block31 : ∀ m : Fin 64,
    forwardTable1 (1984 + m.val) < 2^112 ∧ backwardTable1 (1984 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block32 : ∀ m : Fin 64,
    forwardTable1 (2048 + m.val) < 2^112 ∧ backwardTable1 (2048 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block33 : ∀ m : Fin 64,
    forwardTable1 (2112 + m.val) < 2^112 ∧ backwardTable1 (2112 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block34 : ∀ m : Fin 64,
    forwardTable1 (2176 + m.val) < 2^112 ∧ backwardTable1 (2176 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block35 : ∀ m : Fin 64,
    forwardTable1 (2240 + m.val) < 2^112 ∧ backwardTable1 (2240 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block36 : ∀ m : Fin 64,
    forwardTable1 (2304 + m.val) < 2^112 ∧ backwardTable1 (2304 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block37 : ∀ m : Fin 64,
    forwardTable1 (2368 + m.val) < 2^112 ∧ backwardTable1 (2368 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block38 : ∀ m : Fin 64,
    forwardTable1 (2432 + m.val) < 2^112 ∧ backwardTable1 (2432 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block39 : ∀ m : Fin 64,
    forwardTable1 (2496 + m.val) < 2^112 ∧ backwardTable1 (2496 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block40 : ∀ m : Fin 64,
    forwardTable1 (2560 + m.val) < 2^112 ∧ backwardTable1 (2560 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block41 : ∀ m : Fin 64,
    forwardTable1 (2624 + m.val) < 2^112 ∧ backwardTable1 (2624 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block42 : ∀ m : Fin 64,
    forwardTable1 (2688 + m.val) < 2^112 ∧ backwardTable1 (2688 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block43 : ∀ m : Fin 64,
    forwardTable1 (2752 + m.val) < 2^112 ∧ backwardTable1 (2752 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block44 : ∀ m : Fin 64,
    forwardTable1 (2816 + m.val) < 2^112 ∧ backwardTable1 (2816 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block45 : ∀ m : Fin 64,
    forwardTable1 (2880 + m.val) < 2^112 ∧ backwardTable1 (2880 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block46 : ∀ m : Fin 64,
    forwardTable1 (2944 + m.val) < 2^112 ∧ backwardTable1 (2944 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block47 : ∀ m : Fin 64,
    forwardTable1 (3008 + m.val) < 2^112 ∧ backwardTable1 (3008 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block48 : ∀ m : Fin 64,
    forwardTable1 (3072 + m.val) < 2^112 ∧ backwardTable1 (3072 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block49 : ∀ m : Fin 64,
    forwardTable1 (3136 + m.val) < 2^112 ∧ backwardTable1 (3136 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block50 : ∀ m : Fin 64,
    forwardTable1 (3200 + m.val) < 2^112 ∧ backwardTable1 (3200 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block51 : ∀ m : Fin 64,
    forwardTable1 (3264 + m.val) < 2^112 ∧ backwardTable1 (3264 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block52 : ∀ m : Fin 64,
    forwardTable1 (3328 + m.val) < 2^112 ∧ backwardTable1 (3328 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block53 : ∀ m : Fin 64,
    forwardTable1 (3392 + m.val) < 2^112 ∧ backwardTable1 (3392 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block54 : ∀ m : Fin 64,
    forwardTable1 (3456 + m.val) < 2^112 ∧ backwardTable1 (3456 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block55 : ∀ m : Fin 64,
    forwardTable1 (3520 + m.val) < 2^112 ∧ backwardTable1 (3520 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block56 : ∀ m : Fin 64,
    forwardTable1 (3584 + m.val) < 2^112 ∧ backwardTable1 (3584 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block57 : ∀ m : Fin 64,
    forwardTable1 (3648 + m.val) < 2^112 ∧ backwardTable1 (3648 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block58 : ∀ m : Fin 64,
    forwardTable1 (3712 + m.val) < 2^112 ∧ backwardTable1 (3712 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block59 : ∀ m : Fin 64,
    forwardTable1 (3776 + m.val) < 2^112 ∧ backwardTable1 (3776 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block60 : ∀ m : Fin 64,
    forwardTable1 (3840 + m.val) < 2^112 ∧ backwardTable1 (3840 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block61 : ∀ m : Fin 64,
    forwardTable1 (3904 + m.val) < 2^112 ∧ backwardTable1 (3904 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block62 : ∀ m : Fin 64,
    forwardTable1 (3968 + m.val) < 2^112 ∧ backwardTable1 (3968 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block63 : ∀ m : Fin 64,
    forwardTable1 (4032 + m.val) < 2^112 ∧ backwardTable1 (4032 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block64 : ∀ m : Fin 64,
    forwardTable1 (4096 + m.val) < 2^112 ∧ backwardTable1 (4096 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block65 : ∀ m : Fin 64,
    forwardTable1 (4160 + m.val) < 2^112 ∧ backwardTable1 (4160 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block66 : ∀ m : Fin 64,
    forwardTable1 (4224 + m.val) < 2^112 ∧ backwardTable1 (4224 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block67 : ∀ m : Fin 64,
    forwardTable1 (4288 + m.val) < 2^112 ∧ backwardTable1 (4288 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block68 : ∀ m : Fin 64,
    forwardTable1 (4352 + m.val) < 2^112 ∧ backwardTable1 (4352 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block69 : ∀ m : Fin 64,
    forwardTable1 (4416 + m.val) < 2^112 ∧ backwardTable1 (4416 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block70 : ∀ m : Fin 64,
    forwardTable1 (4480 + m.val) < 2^112 ∧ backwardTable1 (4480 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block71 : ∀ m : Fin 64,
    forwardTable1 (4544 + m.val) < 2^112 ∧ backwardTable1 (4544 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block72 : ∀ m : Fin 64,
    forwardTable1 (4608 + m.val) < 2^112 ∧ backwardTable1 (4608 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block73 : ∀ m : Fin 64,
    forwardTable1 (4672 + m.val) < 2^112 ∧ backwardTable1 (4672 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block74 : ∀ m : Fin 64,
    forwardTable1 (4736 + m.val) < 2^112 ∧ backwardTable1 (4736 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block75 : ∀ m : Fin 64,
    forwardTable1 (4800 + m.val) < 2^112 ∧ backwardTable1 (4800 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block76 : ∀ m : Fin 64,
    forwardTable1 (4864 + m.val) < 2^112 ∧ backwardTable1 (4864 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block77 : ∀ m : Fin 64,
    forwardTable1 (4928 + m.val) < 2^112 ∧ backwardTable1 (4928 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block78 : ∀ m : Fin 64,
    forwardTable1 (4992 + m.val) < 2^112 ∧ backwardTable1 (4992 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block79 : ∀ m : Fin 64,
    forwardTable1 (5056 + m.val) < 2^112 ∧ backwardTable1 (5056 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block80 : ∀ m : Fin 64,
    forwardTable1 (5120 + m.val) < 2^112 ∧ backwardTable1 (5120 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block81 : ∀ m : Fin 64,
    forwardTable1 (5184 + m.val) < 2^112 ∧ backwardTable1 (5184 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block82 : ∀ m : Fin 64,
    forwardTable1 (5248 + m.val) < 2^112 ∧ backwardTable1 (5248 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block83 : ∀ m : Fin 64,
    forwardTable1 (5312 + m.val) < 2^112 ∧ backwardTable1 (5312 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block84 : ∀ m : Fin 64,
    forwardTable1 (5376 + m.val) < 2^112 ∧ backwardTable1 (5376 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block85 : ∀ m : Fin 64,
    forwardTable1 (5440 + m.val) < 2^112 ∧ backwardTable1 (5440 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block86 : ∀ m : Fin 64,
    forwardTable1 (5504 + m.val) < 2^112 ∧ backwardTable1 (5504 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block87 : ∀ m : Fin 64,
    forwardTable1 (5568 + m.val) < 2^112 ∧ backwardTable1 (5568 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block88 : ∀ m : Fin 64,
    forwardTable1 (5632 + m.val) < 2^112 ∧ backwardTable1 (5632 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block89 : ∀ m : Fin 64,
    forwardTable1 (5696 + m.val) < 2^112 ∧ backwardTable1 (5696 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block90 : ∀ m : Fin 64,
    forwardTable1 (5760 + m.val) < 2^112 ∧ backwardTable1 (5760 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block91 : ∀ m : Fin 64,
    forwardTable1 (5824 + m.val) < 2^112 ∧ backwardTable1 (5824 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block92 : ∀ m : Fin 64,
    forwardTable1 (5888 + m.val) < 2^112 ∧ backwardTable1 (5888 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block93 : ∀ m : Fin 64,
    forwardTable1 (5952 + m.val) < 2^112 ∧ backwardTable1 (5952 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block94 : ∀ m : Fin 64,
    forwardTable1 (6016 + m.val) < 2^112 ∧ backwardTable1 (6016 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block95 : ∀ m : Fin 64,
    forwardTable1 (6080 + m.val) < 2^112 ∧ backwardTable1 (6080 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block96 : ∀ m : Fin 64,
    forwardTable1 (6144 + m.val) < 2^112 ∧ backwardTable1 (6144 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block97 : ∀ m : Fin 64,
    forwardTable1 (6208 + m.val) < 2^112 ∧ backwardTable1 (6208 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block98 : ∀ m : Fin 64,
    forwardTable1 (6272 + m.val) < 2^112 ∧ backwardTable1 (6272 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block99 : ∀ m : Fin 64,
    forwardTable1 (6336 + m.val) < 2^112 ∧ backwardTable1 (6336 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block100 : ∀ m : Fin 64,
    forwardTable1 (6400 + m.val) < 2^112 ∧ backwardTable1 (6400 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block101 : ∀ m : Fin 64,
    forwardTable1 (6464 + m.val) < 2^112 ∧ backwardTable1 (6464 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block102 : ∀ m : Fin 64,
    forwardTable1 (6528 + m.val) < 2^112 ∧ backwardTable1 (6528 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block103 : ∀ m : Fin 64,
    forwardTable1 (6592 + m.val) < 2^112 ∧ backwardTable1 (6592 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block104 : ∀ m : Fin 64,
    forwardTable1 (6656 + m.val) < 2^112 ∧ backwardTable1 (6656 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block105 : ∀ m : Fin 64,
    forwardTable1 (6720 + m.val) < 2^112 ∧ backwardTable1 (6720 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block106 : ∀ m : Fin 64,
    forwardTable1 (6784 + m.val) < 2^112 ∧ backwardTable1 (6784 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block107 : ∀ m : Fin 64,
    forwardTable1 (6848 + m.val) < 2^112 ∧ backwardTable1 (6848 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block108 : ∀ m : Fin 64,
    forwardTable1 (6912 + m.val) < 2^112 ∧ backwardTable1 (6912 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block109 : ∀ m : Fin 64,
    forwardTable1 (6976 + m.val) < 2^112 ∧ backwardTable1 (6976 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block110 : ∀ m : Fin 64,
    forwardTable1 (7040 + m.val) < 2^112 ∧ backwardTable1 (7040 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block111 : ∀ m : Fin 64,
    forwardTable1 (7104 + m.val) < 2^112 ∧ backwardTable1 (7104 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block112 : ∀ m : Fin 64,
    forwardTable1 (7168 + m.val) < 2^112 ∧ backwardTable1 (7168 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block113 : ∀ m : Fin 64,
    forwardTable1 (7232 + m.val) < 2^112 ∧ backwardTable1 (7232 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block114 : ∀ m : Fin 64,
    forwardTable1 (7296 + m.val) < 2^112 ∧ backwardTable1 (7296 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block115 : ∀ m : Fin 64,
    forwardTable1 (7360 + m.val) < 2^112 ∧ backwardTable1 (7360 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block116 : ∀ m : Fin 64,
    forwardTable1 (7424 + m.val) < 2^112 ∧ backwardTable1 (7424 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block117 : ∀ m : Fin 64,
    forwardTable1 (7488 + m.val) < 2^112 ∧ backwardTable1 (7488 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block118 : ∀ m : Fin 64,
    forwardTable1 (7552 + m.val) < 2^112 ∧ backwardTable1 (7552 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block119 : ∀ m : Fin 64,
    forwardTable1 (7616 + m.val) < 2^112 ∧ backwardTable1 (7616 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block120 : ∀ m : Fin 64,
    forwardTable1 (7680 + m.val) < 2^112 ∧ backwardTable1 (7680 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block121 : ∀ m : Fin 64,
    forwardTable1 (7744 + m.val) < 2^112 ∧ backwardTable1 (7744 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block122 : ∀ m : Fin 64,
    forwardTable1 (7808 + m.val) < 2^112 ∧ backwardTable1 (7808 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block123 : ∀ m : Fin 64,
    forwardTable1 (7872 + m.val) < 2^112 ∧ backwardTable1 (7872 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block124 : ∀ m : Fin 64,
    forwardTable1 (7936 + m.val) < 2^112 ∧ backwardTable1 (7936 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block125 : ∀ m : Fin 64,
    forwardTable1 (8000 + m.val) < 2^112 ∧ backwardTable1 (8000 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block126 : ∀ m : Fin 64,
    forwardTable1 (8064 + m.val) < 2^112 ∧ backwardTable1 (8064 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds1_block127 : ∀ m : Fin 64,
    forwardTable1 (8128 + m.val) < 2^112 ∧ backwardTable1 (8128 + m.val) < 2^112 := by
  decide +kernel

theorem bounds1 (m : Fin 8192) :
    forwardTable1 m.val < 2^112 ∧ backwardTable1 m.val < 2^112 := by
  apply check_blocks (P := fun a => forwardTable1 a < 2^112 ∧ backwardTable1 a < 2^112)
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact bounds1_block0
  · exact bounds1_block1
  · exact bounds1_block2
  · exact bounds1_block3
  · exact bounds1_block4
  · exact bounds1_block5
  · exact bounds1_block6
  · exact bounds1_block7
  · exact bounds1_block8
  · exact bounds1_block9
  · exact bounds1_block10
  · exact bounds1_block11
  · exact bounds1_block12
  · exact bounds1_block13
  · exact bounds1_block14
  · exact bounds1_block15
  · exact bounds1_block16
  · exact bounds1_block17
  · exact bounds1_block18
  · exact bounds1_block19
  · exact bounds1_block20
  · exact bounds1_block21
  · exact bounds1_block22
  · exact bounds1_block23
  · exact bounds1_block24
  · exact bounds1_block25
  · exact bounds1_block26
  · exact bounds1_block27
  · exact bounds1_block28
  · exact bounds1_block29
  · exact bounds1_block30
  · exact bounds1_block31
  · exact bounds1_block32
  · exact bounds1_block33
  · exact bounds1_block34
  · exact bounds1_block35
  · exact bounds1_block36
  · exact bounds1_block37
  · exact bounds1_block38
  · exact bounds1_block39
  · exact bounds1_block40
  · exact bounds1_block41
  · exact bounds1_block42
  · exact bounds1_block43
  · exact bounds1_block44
  · exact bounds1_block45
  · exact bounds1_block46
  · exact bounds1_block47
  · exact bounds1_block48
  · exact bounds1_block49
  · exact bounds1_block50
  · exact bounds1_block51
  · exact bounds1_block52
  · exact bounds1_block53
  · exact bounds1_block54
  · exact bounds1_block55
  · exact bounds1_block56
  · exact bounds1_block57
  · exact bounds1_block58
  · exact bounds1_block59
  · exact bounds1_block60
  · exact bounds1_block61
  · exact bounds1_block62
  · exact bounds1_block63
  · exact bounds1_block64
  · exact bounds1_block65
  · exact bounds1_block66
  · exact bounds1_block67
  · exact bounds1_block68
  · exact bounds1_block69
  · exact bounds1_block70
  · exact bounds1_block71
  · exact bounds1_block72
  · exact bounds1_block73
  · exact bounds1_block74
  · exact bounds1_block75
  · exact bounds1_block76
  · exact bounds1_block77
  · exact bounds1_block78
  · exact bounds1_block79
  · exact bounds1_block80
  · exact bounds1_block81
  · exact bounds1_block82
  · exact bounds1_block83
  · exact bounds1_block84
  · exact bounds1_block85
  · exact bounds1_block86
  · exact bounds1_block87
  · exact bounds1_block88
  · exact bounds1_block89
  · exact bounds1_block90
  · exact bounds1_block91
  · exact bounds1_block92
  · exact bounds1_block93
  · exact bounds1_block94
  · exact bounds1_block95
  · exact bounds1_block96
  · exact bounds1_block97
  · exact bounds1_block98
  · exact bounds1_block99
  · exact bounds1_block100
  · exact bounds1_block101
  · exact bounds1_block102
  · exact bounds1_block103
  · exact bounds1_block104
  · exact bounds1_block105
  · exact bounds1_block106
  · exact bounds1_block107
  · exact bounds1_block108
  · exact bounds1_block109
  · exact bounds1_block110
  · exact bounds1_block111
  · exact bounds1_block112
  · exact bounds1_block113
  · exact bounds1_block114
  · exact bounds1_block115
  · exact bounds1_block116
  · exact bounds1_block117
  · exact bounds1_block118
  · exact bounds1_block119
  · exact bounds1_block120
  · exact bounds1_block121
  · exact bounds1_block122
  · exact bounds1_block123
  · exact bounds1_block124
  · exact bounds1_block125
  · exact bounds1_block126
  · exact bounds1_block127

set_option maxRecDepth 10000 in
private theorem matches1_block0 : ∀ m : Fin 64,
    (forwardTable1 (0 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (0 + m.val))).val → Listed 1 (0 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block1 : ∀ m : Fin 64,
    (forwardTable1 (64 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (64 + m.val))).val → Listed 1 (64 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block2 : ∀ m : Fin 64,
    (forwardTable1 (128 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (128 + m.val))).val → Listed 1 (128 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block3 : ∀ m : Fin 64,
    (forwardTable1 (192 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (192 + m.val))).val → Listed 1 (192 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block4 : ∀ m : Fin 64,
    (forwardTable1 (256 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (256 + m.val))).val → Listed 1 (256 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block5 : ∀ m : Fin 64,
    (forwardTable1 (320 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (320 + m.val))).val → Listed 1 (320 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block6 : ∀ m : Fin 64,
    (forwardTable1 (384 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (384 + m.val))).val → Listed 1 (384 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block7 : ∀ m : Fin 64,
    (forwardTable1 (448 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (448 + m.val))).val → Listed 1 (448 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block8 : ∀ m : Fin 64,
    (forwardTable1 (512 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (512 + m.val))).val → Listed 1 (512 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block9 : ∀ m : Fin 64,
    (forwardTable1 (576 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (576 + m.val))).val → Listed 1 (576 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block10 : ∀ m : Fin 64,
    (forwardTable1 (640 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (640 + m.val))).val → Listed 1 (640 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block11 : ∀ m : Fin 64,
    (forwardTable1 (704 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (704 + m.val))).val → Listed 1 (704 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block12 : ∀ m : Fin 64,
    (forwardTable1 (768 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (768 + m.val))).val → Listed 1 (768 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block13 : ∀ m : Fin 64,
    (forwardTable1 (832 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (832 + m.val))).val → Listed 1 (832 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block14 : ∀ m : Fin 64,
    (forwardTable1 (896 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (896 + m.val))).val → Listed 1 (896 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block15 : ∀ m : Fin 64,
    (forwardTable1 (960 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (960 + m.val))).val → Listed 1 (960 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block16 : ∀ m : Fin 64,
    (forwardTable1 (1024 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1024 + m.val))).val → Listed 1 (1024 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block17 : ∀ m : Fin 64,
    (forwardTable1 (1088 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1088 + m.val))).val → Listed 1 (1088 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block18 : ∀ m : Fin 64,
    (forwardTable1 (1152 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1152 + m.val))).val → Listed 1 (1152 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block19 : ∀ m : Fin 64,
    (forwardTable1 (1216 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1216 + m.val))).val → Listed 1 (1216 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block20 : ∀ m : Fin 64,
    (forwardTable1 (1280 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1280 + m.val))).val → Listed 1 (1280 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block21 : ∀ m : Fin 64,
    (forwardTable1 (1344 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1344 + m.val))).val → Listed 1 (1344 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block22 : ∀ m : Fin 64,
    (forwardTable1 (1408 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1408 + m.val))).val → Listed 1 (1408 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block23 : ∀ m : Fin 64,
    (forwardTable1 (1472 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1472 + m.val))).val → Listed 1 (1472 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block24 : ∀ m : Fin 64,
    (forwardTable1 (1536 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1536 + m.val))).val → Listed 1 (1536 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block25 : ∀ m : Fin 64,
    (forwardTable1 (1600 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1600 + m.val))).val → Listed 1 (1600 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block26 : ∀ m : Fin 64,
    (forwardTable1 (1664 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1664 + m.val))).val → Listed 1 (1664 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block27 : ∀ m : Fin 64,
    (forwardTable1 (1728 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1728 + m.val))).val → Listed 1 (1728 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block28 : ∀ m : Fin 64,
    (forwardTable1 (1792 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1792 + m.val))).val → Listed 1 (1792 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block29 : ∀ m : Fin 64,
    (forwardTable1 (1856 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1856 + m.val))).val → Listed 1 (1856 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block30 : ∀ m : Fin 64,
    (forwardTable1 (1920 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1920 + m.val))).val → Listed 1 (1920 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block31 : ∀ m : Fin 64,
    (forwardTable1 (1984 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (1984 + m.val))).val → Listed 1 (1984 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block32 : ∀ m : Fin 64,
    (forwardTable1 (2048 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2048 + m.val))).val → Listed 1 (2048 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block33 : ∀ m : Fin 64,
    (forwardTable1 (2112 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2112 + m.val))).val → Listed 1 (2112 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block34 : ∀ m : Fin 64,
    (forwardTable1 (2176 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2176 + m.val))).val → Listed 1 (2176 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block35 : ∀ m : Fin 64,
    (forwardTable1 (2240 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2240 + m.val))).val → Listed 1 (2240 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block36 : ∀ m : Fin 64,
    (forwardTable1 (2304 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2304 + m.val))).val → Listed 1 (2304 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block37 : ∀ m : Fin 64,
    (forwardTable1 (2368 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2368 + m.val))).val → Listed 1 (2368 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block38 : ∀ m : Fin 64,
    (forwardTable1 (2432 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2432 + m.val))).val → Listed 1 (2432 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block39 : ∀ m : Fin 64,
    (forwardTable1 (2496 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2496 + m.val))).val → Listed 1 (2496 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block40 : ∀ m : Fin 64,
    (forwardTable1 (2560 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2560 + m.val))).val → Listed 1 (2560 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block41 : ∀ m : Fin 64,
    (forwardTable1 (2624 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2624 + m.val))).val → Listed 1 (2624 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block42 : ∀ m : Fin 64,
    (forwardTable1 (2688 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2688 + m.val))).val → Listed 1 (2688 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block43 : ∀ m : Fin 64,
    (forwardTable1 (2752 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2752 + m.val))).val → Listed 1 (2752 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block44 : ∀ m : Fin 64,
    (forwardTable1 (2816 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2816 + m.val))).val → Listed 1 (2816 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block45 : ∀ m : Fin 64,
    (forwardTable1 (2880 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2880 + m.val))).val → Listed 1 (2880 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block46 : ∀ m : Fin 64,
    (forwardTable1 (2944 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (2944 + m.val))).val → Listed 1 (2944 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block47 : ∀ m : Fin 64,
    (forwardTable1 (3008 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3008 + m.val))).val → Listed 1 (3008 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block48 : ∀ m : Fin 64,
    (forwardTable1 (3072 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3072 + m.val))).val → Listed 1 (3072 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block49 : ∀ m : Fin 64,
    (forwardTable1 (3136 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3136 + m.val))).val → Listed 1 (3136 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block50 : ∀ m : Fin 64,
    (forwardTable1 (3200 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3200 + m.val))).val → Listed 1 (3200 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block51 : ∀ m : Fin 64,
    (forwardTable1 (3264 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3264 + m.val))).val → Listed 1 (3264 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block52 : ∀ m : Fin 64,
    (forwardTable1 (3328 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3328 + m.val))).val → Listed 1 (3328 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block53 : ∀ m : Fin 64,
    (forwardTable1 (3392 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3392 + m.val))).val → Listed 1 (3392 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block54 : ∀ m : Fin 64,
    (forwardTable1 (3456 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3456 + m.val))).val → Listed 1 (3456 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block55 : ∀ m : Fin 64,
    (forwardTable1 (3520 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3520 + m.val))).val → Listed 1 (3520 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block56 : ∀ m : Fin 64,
    (forwardTable1 (3584 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3584 + m.val))).val → Listed 1 (3584 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block57 : ∀ m : Fin 64,
    (forwardTable1 (3648 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3648 + m.val))).val → Listed 1 (3648 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block58 : ∀ m : Fin 64,
    (forwardTable1 (3712 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3712 + m.val))).val → Listed 1 (3712 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block59 : ∀ m : Fin 64,
    (forwardTable1 (3776 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3776 + m.val))).val → Listed 1 (3776 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block60 : ∀ m : Fin 64,
    (forwardTable1 (3840 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3840 + m.val))).val → Listed 1 (3840 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block61 : ∀ m : Fin 64,
    (forwardTable1 (3904 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3904 + m.val))).val → Listed 1 (3904 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block62 : ∀ m : Fin 64,
    (forwardTable1 (3968 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (3968 + m.val))).val → Listed 1 (3968 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block63 : ∀ m : Fin 64,
    (forwardTable1 (4032 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4032 + m.val))).val → Listed 1 (4032 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block64 : ∀ m : Fin 64,
    (forwardTable1 (4096 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4096 + m.val))).val → Listed 1 (4096 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block65 : ∀ m : Fin 64,
    (forwardTable1 (4160 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4160 + m.val))).val → Listed 1 (4160 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block66 : ∀ m : Fin 64,
    (forwardTable1 (4224 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4224 + m.val))).val → Listed 1 (4224 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block67 : ∀ m : Fin 64,
    (forwardTable1 (4288 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4288 + m.val))).val → Listed 1 (4288 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block68 : ∀ m : Fin 64,
    (forwardTable1 (4352 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4352 + m.val))).val → Listed 1 (4352 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block69 : ∀ m : Fin 64,
    (forwardTable1 (4416 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4416 + m.val))).val → Listed 1 (4416 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block70 : ∀ m : Fin 64,
    (forwardTable1 (4480 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4480 + m.val))).val → Listed 1 (4480 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block71 : ∀ m : Fin 64,
    (forwardTable1 (4544 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4544 + m.val))).val → Listed 1 (4544 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block72 : ∀ m : Fin 64,
    (forwardTable1 (4608 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4608 + m.val))).val → Listed 1 (4608 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block73 : ∀ m : Fin 64,
    (forwardTable1 (4672 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4672 + m.val))).val → Listed 1 (4672 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block74 : ∀ m : Fin 64,
    (forwardTable1 (4736 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4736 + m.val))).val → Listed 1 (4736 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block75 : ∀ m : Fin 64,
    (forwardTable1 (4800 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4800 + m.val))).val → Listed 1 (4800 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block76 : ∀ m : Fin 64,
    (forwardTable1 (4864 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4864 + m.val))).val → Listed 1 (4864 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block77 : ∀ m : Fin 64,
    (forwardTable1 (4928 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4928 + m.val))).val → Listed 1 (4928 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block78 : ∀ m : Fin 64,
    (forwardTable1 (4992 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (4992 + m.val))).val → Listed 1 (4992 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block79 : ∀ m : Fin 64,
    (forwardTable1 (5056 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5056 + m.val))).val → Listed 1 (5056 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block80 : ∀ m : Fin 64,
    (forwardTable1 (5120 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5120 + m.val))).val → Listed 1 (5120 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block81 : ∀ m : Fin 64,
    (forwardTable1 (5184 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5184 + m.val))).val → Listed 1 (5184 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block82 : ∀ m : Fin 64,
    (forwardTable1 (5248 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5248 + m.val))).val → Listed 1 (5248 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block83 : ∀ m : Fin 64,
    (forwardTable1 (5312 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5312 + m.val))).val → Listed 1 (5312 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block84 : ∀ m : Fin 64,
    (forwardTable1 (5376 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5376 + m.val))).val → Listed 1 (5376 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block85 : ∀ m : Fin 64,
    (forwardTable1 (5440 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5440 + m.val))).val → Listed 1 (5440 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block86 : ∀ m : Fin 64,
    (forwardTable1 (5504 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5504 + m.val))).val → Listed 1 (5504 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block87 : ∀ m : Fin 64,
    (forwardTable1 (5568 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5568 + m.val))).val → Listed 1 (5568 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block88 : ∀ m : Fin 64,
    (forwardTable1 (5632 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5632 + m.val))).val → Listed 1 (5632 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block89 : ∀ m : Fin 64,
    (forwardTable1 (5696 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5696 + m.val))).val → Listed 1 (5696 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block90 : ∀ m : Fin 64,
    (forwardTable1 (5760 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5760 + m.val))).val → Listed 1 (5760 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block91 : ∀ m : Fin 64,
    (forwardTable1 (5824 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5824 + m.val))).val → Listed 1 (5824 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block92 : ∀ m : Fin 64,
    (forwardTable1 (5888 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5888 + m.val))).val → Listed 1 (5888 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block93 : ∀ m : Fin 64,
    (forwardTable1 (5952 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (5952 + m.val))).val → Listed 1 (5952 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block94 : ∀ m : Fin 64,
    (forwardTable1 (6016 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6016 + m.val))).val → Listed 1 (6016 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block95 : ∀ m : Fin 64,
    (forwardTable1 (6080 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6080 + m.val))).val → Listed 1 (6080 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block96 : ∀ m : Fin 64,
    (forwardTable1 (6144 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6144 + m.val))).val → Listed 1 (6144 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block97 : ∀ m : Fin 64,
    (forwardTable1 (6208 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6208 + m.val))).val → Listed 1 (6208 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block98 : ∀ m : Fin 64,
    (forwardTable1 (6272 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6272 + m.val))).val → Listed 1 (6272 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block99 : ∀ m : Fin 64,
    (forwardTable1 (6336 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6336 + m.val))).val → Listed 1 (6336 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block100 : ∀ m : Fin 64,
    (forwardTable1 (6400 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6400 + m.val))).val → Listed 1 (6400 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block101 : ∀ m : Fin 64,
    (forwardTable1 (6464 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6464 + m.val))).val → Listed 1 (6464 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block102 : ∀ m : Fin 64,
    (forwardTable1 (6528 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6528 + m.val))).val → Listed 1 (6528 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block103 : ∀ m : Fin 64,
    (forwardTable1 (6592 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6592 + m.val))).val → Listed 1 (6592 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block104 : ∀ m : Fin 64,
    (forwardTable1 (6656 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6656 + m.val))).val → Listed 1 (6656 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block105 : ∀ m : Fin 64,
    (forwardTable1 (6720 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6720 + m.val))).val → Listed 1 (6720 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block106 : ∀ m : Fin 64,
    (forwardTable1 (6784 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6784 + m.val))).val → Listed 1 (6784 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block107 : ∀ m : Fin 64,
    (forwardTable1 (6848 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6848 + m.val))).val → Listed 1 (6848 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block108 : ∀ m : Fin 64,
    (forwardTable1 (6912 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6912 + m.val))).val → Listed 1 (6912 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block109 : ∀ m : Fin 64,
    (forwardTable1 (6976 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (6976 + m.val))).val → Listed 1 (6976 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block110 : ∀ m : Fin 64,
    (forwardTable1 (7040 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7040 + m.val))).val → Listed 1 (7040 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block111 : ∀ m : Fin 64,
    (forwardTable1 (7104 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7104 + m.val))).val → Listed 1 (7104 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block112 : ∀ m : Fin 64,
    (forwardTable1 (7168 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7168 + m.val))).val → Listed 1 (7168 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block113 : ∀ m : Fin 64,
    (forwardTable1 (7232 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7232 + m.val))).val → Listed 1 (7232 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block114 : ∀ m : Fin 64,
    (forwardTable1 (7296 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7296 + m.val))).val → Listed 1 (7296 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block115 : ∀ m : Fin 64,
    (forwardTable1 (7360 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7360 + m.val))).val → Listed 1 (7360 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block116 : ∀ m : Fin 64,
    (forwardTable1 (7424 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7424 + m.val))).val → Listed 1 (7424 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block117 : ∀ m : Fin 64,
    (forwardTable1 (7488 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7488 + m.val))).val → Listed 1 (7488 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block118 : ∀ m : Fin 64,
    (forwardTable1 (7552 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7552 + m.val))).val → Listed 1 (7552 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block119 : ∀ m : Fin 64,
    (forwardTable1 (7616 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7616 + m.val))).val → Listed 1 (7616 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block120 : ∀ m : Fin 64,
    (forwardTable1 (7680 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7680 + m.val))).val → Listed 1 (7680 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block121 : ∀ m : Fin 64,
    (forwardTable1 (7744 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7744 + m.val))).val → Listed 1 (7744 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block122 : ∀ m : Fin 64,
    (forwardTable1 (7808 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7808 + m.val))).val → Listed 1 (7808 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block123 : ∀ m : Fin 64,
    (forwardTable1 (7872 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7872 + m.val))).val → Listed 1 (7872 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block124 : ∀ m : Fin 64,
    (forwardTable1 (7936 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (7936 + m.val))).val → Listed 1 (7936 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block125 : ∀ m : Fin 64,
    (forwardTable1 (8000 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (8000 + m.val))).val → Listed 1 (8000 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block126 : ∀ m : Fin 64,
    (forwardTable1 (8064 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (8064 + m.val))).val → Listed 1 (8064 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches1_block127 : ∀ m : Fin 64,
    (forwardTable1 (8128 + m.val) = backwardTable1 (reverseCode (Fin.ofNat 8192 (8128 + m.val))).val → Listed 1 (8128 + m.val)) := by
  decide +kernel

theorem matches1 (m : Fin 8192) :
    (forwardTable1 m.val = backwardTable1 (reverseCode (Fin.ofNat 8192 m.val)).val → Listed 1 m.val) := by
  apply check_blocks (P := fun a => (forwardTable1 a = backwardTable1 (reverseCode (Fin.ofNat 8192 a)).val → Listed 1 a))
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact matches1_block0
  · exact matches1_block1
  · exact matches1_block2
  · exact matches1_block3
  · exact matches1_block4
  · exact matches1_block5
  · exact matches1_block6
  · exact matches1_block7
  · exact matches1_block8
  · exact matches1_block9
  · exact matches1_block10
  · exact matches1_block11
  · exact matches1_block12
  · exact matches1_block13
  · exact matches1_block14
  · exact matches1_block15
  · exact matches1_block16
  · exact matches1_block17
  · exact matches1_block18
  · exact matches1_block19
  · exact matches1_block20
  · exact matches1_block21
  · exact matches1_block22
  · exact matches1_block23
  · exact matches1_block24
  · exact matches1_block25
  · exact matches1_block26
  · exact matches1_block27
  · exact matches1_block28
  · exact matches1_block29
  · exact matches1_block30
  · exact matches1_block31
  · exact matches1_block32
  · exact matches1_block33
  · exact matches1_block34
  · exact matches1_block35
  · exact matches1_block36
  · exact matches1_block37
  · exact matches1_block38
  · exact matches1_block39
  · exact matches1_block40
  · exact matches1_block41
  · exact matches1_block42
  · exact matches1_block43
  · exact matches1_block44
  · exact matches1_block45
  · exact matches1_block46
  · exact matches1_block47
  · exact matches1_block48
  · exact matches1_block49
  · exact matches1_block50
  · exact matches1_block51
  · exact matches1_block52
  · exact matches1_block53
  · exact matches1_block54
  · exact matches1_block55
  · exact matches1_block56
  · exact matches1_block57
  · exact matches1_block58
  · exact matches1_block59
  · exact matches1_block60
  · exact matches1_block61
  · exact matches1_block62
  · exact matches1_block63
  · exact matches1_block64
  · exact matches1_block65
  · exact matches1_block66
  · exact matches1_block67
  · exact matches1_block68
  · exact matches1_block69
  · exact matches1_block70
  · exact matches1_block71
  · exact matches1_block72
  · exact matches1_block73
  · exact matches1_block74
  · exact matches1_block75
  · exact matches1_block76
  · exact matches1_block77
  · exact matches1_block78
  · exact matches1_block79
  · exact matches1_block80
  · exact matches1_block81
  · exact matches1_block82
  · exact matches1_block83
  · exact matches1_block84
  · exact matches1_block85
  · exact matches1_block86
  · exact matches1_block87
  · exact matches1_block88
  · exact matches1_block89
  · exact matches1_block90
  · exact matches1_block91
  · exact matches1_block92
  · exact matches1_block93
  · exact matches1_block94
  · exact matches1_block95
  · exact matches1_block96
  · exact matches1_block97
  · exact matches1_block98
  · exact matches1_block99
  · exact matches1_block100
  · exact matches1_block101
  · exact matches1_block102
  · exact matches1_block103
  · exact matches1_block104
  · exact matches1_block105
  · exact matches1_block106
  · exact matches1_block107
  · exact matches1_block108
  · exact matches1_block109
  · exact matches1_block110
  · exact matches1_block111
  · exact matches1_block112
  · exact matches1_block113
  · exact matches1_block114
  · exact matches1_block115
  · exact matches1_block116
  · exact matches1_block117
  · exact matches1_block118
  · exact matches1_block119
  · exact matches1_block120
  · exact matches1_block121
  · exact matches1_block122
  · exact matches1_block123
  · exact matches1_block124
  · exact matches1_block125
  · exact matches1_block126
  · exact matches1_block127


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
