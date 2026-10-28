module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber0
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Witnesses

/-!
# Bounds and mask witnesses for fiber 0

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
theorem backward_zero0 : backwardTable0 0 = liftEntry 0 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block0 : ∀ m : Fin 64,
    forwardTable0 (0 + m.val) < 2^112 ∧ backwardTable0 (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block1 : ∀ m : Fin 64,
    forwardTable0 (64 + m.val) < 2^112 ∧ backwardTable0 (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block2 : ∀ m : Fin 64,
    forwardTable0 (128 + m.val) < 2^112 ∧ backwardTable0 (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block3 : ∀ m : Fin 64,
    forwardTable0 (192 + m.val) < 2^112 ∧ backwardTable0 (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block4 : ∀ m : Fin 64,
    forwardTable0 (256 + m.val) < 2^112 ∧ backwardTable0 (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block5 : ∀ m : Fin 64,
    forwardTable0 (320 + m.val) < 2^112 ∧ backwardTable0 (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block6 : ∀ m : Fin 64,
    forwardTable0 (384 + m.val) < 2^112 ∧ backwardTable0 (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block7 : ∀ m : Fin 64,
    forwardTable0 (448 + m.val) < 2^112 ∧ backwardTable0 (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block8 : ∀ m : Fin 64,
    forwardTable0 (512 + m.val) < 2^112 ∧ backwardTable0 (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block9 : ∀ m : Fin 64,
    forwardTable0 (576 + m.val) < 2^112 ∧ backwardTable0 (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block10 : ∀ m : Fin 64,
    forwardTable0 (640 + m.val) < 2^112 ∧ backwardTable0 (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block11 : ∀ m : Fin 64,
    forwardTable0 (704 + m.val) < 2^112 ∧ backwardTable0 (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block12 : ∀ m : Fin 64,
    forwardTable0 (768 + m.val) < 2^112 ∧ backwardTable0 (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block13 : ∀ m : Fin 64,
    forwardTable0 (832 + m.val) < 2^112 ∧ backwardTable0 (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block14 : ∀ m : Fin 64,
    forwardTable0 (896 + m.val) < 2^112 ∧ backwardTable0 (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block15 : ∀ m : Fin 64,
    forwardTable0 (960 + m.val) < 2^112 ∧ backwardTable0 (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block16 : ∀ m : Fin 64,
    forwardTable0 (1024 + m.val) < 2^112 ∧ backwardTable0 (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block17 : ∀ m : Fin 64,
    forwardTable0 (1088 + m.val) < 2^112 ∧ backwardTable0 (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block18 : ∀ m : Fin 64,
    forwardTable0 (1152 + m.val) < 2^112 ∧ backwardTable0 (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block19 : ∀ m : Fin 64,
    forwardTable0 (1216 + m.val) < 2^112 ∧ backwardTable0 (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block20 : ∀ m : Fin 64,
    forwardTable0 (1280 + m.val) < 2^112 ∧ backwardTable0 (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block21 : ∀ m : Fin 64,
    forwardTable0 (1344 + m.val) < 2^112 ∧ backwardTable0 (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block22 : ∀ m : Fin 64,
    forwardTable0 (1408 + m.val) < 2^112 ∧ backwardTable0 (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block23 : ∀ m : Fin 64,
    forwardTable0 (1472 + m.val) < 2^112 ∧ backwardTable0 (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block24 : ∀ m : Fin 64,
    forwardTable0 (1536 + m.val) < 2^112 ∧ backwardTable0 (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block25 : ∀ m : Fin 64,
    forwardTable0 (1600 + m.val) < 2^112 ∧ backwardTable0 (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block26 : ∀ m : Fin 64,
    forwardTable0 (1664 + m.val) < 2^112 ∧ backwardTable0 (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block27 : ∀ m : Fin 64,
    forwardTable0 (1728 + m.val) < 2^112 ∧ backwardTable0 (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block28 : ∀ m : Fin 64,
    forwardTable0 (1792 + m.val) < 2^112 ∧ backwardTable0 (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block29 : ∀ m : Fin 64,
    forwardTable0 (1856 + m.val) < 2^112 ∧ backwardTable0 (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block30 : ∀ m : Fin 64,
    forwardTable0 (1920 + m.val) < 2^112 ∧ backwardTable0 (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block31 : ∀ m : Fin 64,
    forwardTable0 (1984 + m.val) < 2^112 ∧ backwardTable0 (1984 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block32 : ∀ m : Fin 64,
    forwardTable0 (2048 + m.val) < 2^112 ∧ backwardTable0 (2048 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block33 : ∀ m : Fin 64,
    forwardTable0 (2112 + m.val) < 2^112 ∧ backwardTable0 (2112 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block34 : ∀ m : Fin 64,
    forwardTable0 (2176 + m.val) < 2^112 ∧ backwardTable0 (2176 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block35 : ∀ m : Fin 64,
    forwardTable0 (2240 + m.val) < 2^112 ∧ backwardTable0 (2240 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block36 : ∀ m : Fin 64,
    forwardTable0 (2304 + m.val) < 2^112 ∧ backwardTable0 (2304 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block37 : ∀ m : Fin 64,
    forwardTable0 (2368 + m.val) < 2^112 ∧ backwardTable0 (2368 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block38 : ∀ m : Fin 64,
    forwardTable0 (2432 + m.val) < 2^112 ∧ backwardTable0 (2432 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block39 : ∀ m : Fin 64,
    forwardTable0 (2496 + m.val) < 2^112 ∧ backwardTable0 (2496 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block40 : ∀ m : Fin 64,
    forwardTable0 (2560 + m.val) < 2^112 ∧ backwardTable0 (2560 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block41 : ∀ m : Fin 64,
    forwardTable0 (2624 + m.val) < 2^112 ∧ backwardTable0 (2624 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block42 : ∀ m : Fin 64,
    forwardTable0 (2688 + m.val) < 2^112 ∧ backwardTable0 (2688 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block43 : ∀ m : Fin 64,
    forwardTable0 (2752 + m.val) < 2^112 ∧ backwardTable0 (2752 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block44 : ∀ m : Fin 64,
    forwardTable0 (2816 + m.val) < 2^112 ∧ backwardTable0 (2816 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block45 : ∀ m : Fin 64,
    forwardTable0 (2880 + m.val) < 2^112 ∧ backwardTable0 (2880 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block46 : ∀ m : Fin 64,
    forwardTable0 (2944 + m.val) < 2^112 ∧ backwardTable0 (2944 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block47 : ∀ m : Fin 64,
    forwardTable0 (3008 + m.val) < 2^112 ∧ backwardTable0 (3008 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block48 : ∀ m : Fin 64,
    forwardTable0 (3072 + m.val) < 2^112 ∧ backwardTable0 (3072 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block49 : ∀ m : Fin 64,
    forwardTable0 (3136 + m.val) < 2^112 ∧ backwardTable0 (3136 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block50 : ∀ m : Fin 64,
    forwardTable0 (3200 + m.val) < 2^112 ∧ backwardTable0 (3200 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block51 : ∀ m : Fin 64,
    forwardTable0 (3264 + m.val) < 2^112 ∧ backwardTable0 (3264 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block52 : ∀ m : Fin 64,
    forwardTable0 (3328 + m.val) < 2^112 ∧ backwardTable0 (3328 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block53 : ∀ m : Fin 64,
    forwardTable0 (3392 + m.val) < 2^112 ∧ backwardTable0 (3392 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block54 : ∀ m : Fin 64,
    forwardTable0 (3456 + m.val) < 2^112 ∧ backwardTable0 (3456 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block55 : ∀ m : Fin 64,
    forwardTable0 (3520 + m.val) < 2^112 ∧ backwardTable0 (3520 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block56 : ∀ m : Fin 64,
    forwardTable0 (3584 + m.val) < 2^112 ∧ backwardTable0 (3584 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block57 : ∀ m : Fin 64,
    forwardTable0 (3648 + m.val) < 2^112 ∧ backwardTable0 (3648 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block58 : ∀ m : Fin 64,
    forwardTable0 (3712 + m.val) < 2^112 ∧ backwardTable0 (3712 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block59 : ∀ m : Fin 64,
    forwardTable0 (3776 + m.val) < 2^112 ∧ backwardTable0 (3776 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block60 : ∀ m : Fin 64,
    forwardTable0 (3840 + m.val) < 2^112 ∧ backwardTable0 (3840 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block61 : ∀ m : Fin 64,
    forwardTable0 (3904 + m.val) < 2^112 ∧ backwardTable0 (3904 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block62 : ∀ m : Fin 64,
    forwardTable0 (3968 + m.val) < 2^112 ∧ backwardTable0 (3968 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block63 : ∀ m : Fin 64,
    forwardTable0 (4032 + m.val) < 2^112 ∧ backwardTable0 (4032 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block64 : ∀ m : Fin 64,
    forwardTable0 (4096 + m.val) < 2^112 ∧ backwardTable0 (4096 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block65 : ∀ m : Fin 64,
    forwardTable0 (4160 + m.val) < 2^112 ∧ backwardTable0 (4160 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block66 : ∀ m : Fin 64,
    forwardTable0 (4224 + m.val) < 2^112 ∧ backwardTable0 (4224 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block67 : ∀ m : Fin 64,
    forwardTable0 (4288 + m.val) < 2^112 ∧ backwardTable0 (4288 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block68 : ∀ m : Fin 64,
    forwardTable0 (4352 + m.val) < 2^112 ∧ backwardTable0 (4352 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block69 : ∀ m : Fin 64,
    forwardTable0 (4416 + m.val) < 2^112 ∧ backwardTable0 (4416 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block70 : ∀ m : Fin 64,
    forwardTable0 (4480 + m.val) < 2^112 ∧ backwardTable0 (4480 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block71 : ∀ m : Fin 64,
    forwardTable0 (4544 + m.val) < 2^112 ∧ backwardTable0 (4544 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block72 : ∀ m : Fin 64,
    forwardTable0 (4608 + m.val) < 2^112 ∧ backwardTable0 (4608 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block73 : ∀ m : Fin 64,
    forwardTable0 (4672 + m.val) < 2^112 ∧ backwardTable0 (4672 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block74 : ∀ m : Fin 64,
    forwardTable0 (4736 + m.val) < 2^112 ∧ backwardTable0 (4736 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block75 : ∀ m : Fin 64,
    forwardTable0 (4800 + m.val) < 2^112 ∧ backwardTable0 (4800 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block76 : ∀ m : Fin 64,
    forwardTable0 (4864 + m.val) < 2^112 ∧ backwardTable0 (4864 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block77 : ∀ m : Fin 64,
    forwardTable0 (4928 + m.val) < 2^112 ∧ backwardTable0 (4928 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block78 : ∀ m : Fin 64,
    forwardTable0 (4992 + m.val) < 2^112 ∧ backwardTable0 (4992 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block79 : ∀ m : Fin 64,
    forwardTable0 (5056 + m.val) < 2^112 ∧ backwardTable0 (5056 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block80 : ∀ m : Fin 64,
    forwardTable0 (5120 + m.val) < 2^112 ∧ backwardTable0 (5120 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block81 : ∀ m : Fin 64,
    forwardTable0 (5184 + m.val) < 2^112 ∧ backwardTable0 (5184 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block82 : ∀ m : Fin 64,
    forwardTable0 (5248 + m.val) < 2^112 ∧ backwardTable0 (5248 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block83 : ∀ m : Fin 64,
    forwardTable0 (5312 + m.val) < 2^112 ∧ backwardTable0 (5312 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block84 : ∀ m : Fin 64,
    forwardTable0 (5376 + m.val) < 2^112 ∧ backwardTable0 (5376 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block85 : ∀ m : Fin 64,
    forwardTable0 (5440 + m.val) < 2^112 ∧ backwardTable0 (5440 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block86 : ∀ m : Fin 64,
    forwardTable0 (5504 + m.val) < 2^112 ∧ backwardTable0 (5504 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block87 : ∀ m : Fin 64,
    forwardTable0 (5568 + m.val) < 2^112 ∧ backwardTable0 (5568 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block88 : ∀ m : Fin 64,
    forwardTable0 (5632 + m.val) < 2^112 ∧ backwardTable0 (5632 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block89 : ∀ m : Fin 64,
    forwardTable0 (5696 + m.val) < 2^112 ∧ backwardTable0 (5696 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block90 : ∀ m : Fin 64,
    forwardTable0 (5760 + m.val) < 2^112 ∧ backwardTable0 (5760 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block91 : ∀ m : Fin 64,
    forwardTable0 (5824 + m.val) < 2^112 ∧ backwardTable0 (5824 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block92 : ∀ m : Fin 64,
    forwardTable0 (5888 + m.val) < 2^112 ∧ backwardTable0 (5888 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block93 : ∀ m : Fin 64,
    forwardTable0 (5952 + m.val) < 2^112 ∧ backwardTable0 (5952 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block94 : ∀ m : Fin 64,
    forwardTable0 (6016 + m.val) < 2^112 ∧ backwardTable0 (6016 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block95 : ∀ m : Fin 64,
    forwardTable0 (6080 + m.val) < 2^112 ∧ backwardTable0 (6080 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block96 : ∀ m : Fin 64,
    forwardTable0 (6144 + m.val) < 2^112 ∧ backwardTable0 (6144 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block97 : ∀ m : Fin 64,
    forwardTable0 (6208 + m.val) < 2^112 ∧ backwardTable0 (6208 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block98 : ∀ m : Fin 64,
    forwardTable0 (6272 + m.val) < 2^112 ∧ backwardTable0 (6272 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block99 : ∀ m : Fin 64,
    forwardTable0 (6336 + m.val) < 2^112 ∧ backwardTable0 (6336 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block100 : ∀ m : Fin 64,
    forwardTable0 (6400 + m.val) < 2^112 ∧ backwardTable0 (6400 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block101 : ∀ m : Fin 64,
    forwardTable0 (6464 + m.val) < 2^112 ∧ backwardTable0 (6464 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block102 : ∀ m : Fin 64,
    forwardTable0 (6528 + m.val) < 2^112 ∧ backwardTable0 (6528 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block103 : ∀ m : Fin 64,
    forwardTable0 (6592 + m.val) < 2^112 ∧ backwardTable0 (6592 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block104 : ∀ m : Fin 64,
    forwardTable0 (6656 + m.val) < 2^112 ∧ backwardTable0 (6656 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block105 : ∀ m : Fin 64,
    forwardTable0 (6720 + m.val) < 2^112 ∧ backwardTable0 (6720 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block106 : ∀ m : Fin 64,
    forwardTable0 (6784 + m.val) < 2^112 ∧ backwardTable0 (6784 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block107 : ∀ m : Fin 64,
    forwardTable0 (6848 + m.val) < 2^112 ∧ backwardTable0 (6848 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block108 : ∀ m : Fin 64,
    forwardTable0 (6912 + m.val) < 2^112 ∧ backwardTable0 (6912 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block109 : ∀ m : Fin 64,
    forwardTable0 (6976 + m.val) < 2^112 ∧ backwardTable0 (6976 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block110 : ∀ m : Fin 64,
    forwardTable0 (7040 + m.val) < 2^112 ∧ backwardTable0 (7040 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block111 : ∀ m : Fin 64,
    forwardTable0 (7104 + m.val) < 2^112 ∧ backwardTable0 (7104 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block112 : ∀ m : Fin 64,
    forwardTable0 (7168 + m.val) < 2^112 ∧ backwardTable0 (7168 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block113 : ∀ m : Fin 64,
    forwardTable0 (7232 + m.val) < 2^112 ∧ backwardTable0 (7232 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block114 : ∀ m : Fin 64,
    forwardTable0 (7296 + m.val) < 2^112 ∧ backwardTable0 (7296 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block115 : ∀ m : Fin 64,
    forwardTable0 (7360 + m.val) < 2^112 ∧ backwardTable0 (7360 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block116 : ∀ m : Fin 64,
    forwardTable0 (7424 + m.val) < 2^112 ∧ backwardTable0 (7424 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block117 : ∀ m : Fin 64,
    forwardTable0 (7488 + m.val) < 2^112 ∧ backwardTable0 (7488 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block118 : ∀ m : Fin 64,
    forwardTable0 (7552 + m.val) < 2^112 ∧ backwardTable0 (7552 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block119 : ∀ m : Fin 64,
    forwardTable0 (7616 + m.val) < 2^112 ∧ backwardTable0 (7616 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block120 : ∀ m : Fin 64,
    forwardTable0 (7680 + m.val) < 2^112 ∧ backwardTable0 (7680 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block121 : ∀ m : Fin 64,
    forwardTable0 (7744 + m.val) < 2^112 ∧ backwardTable0 (7744 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block122 : ∀ m : Fin 64,
    forwardTable0 (7808 + m.val) < 2^112 ∧ backwardTable0 (7808 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block123 : ∀ m : Fin 64,
    forwardTable0 (7872 + m.val) < 2^112 ∧ backwardTable0 (7872 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block124 : ∀ m : Fin 64,
    forwardTable0 (7936 + m.val) < 2^112 ∧ backwardTable0 (7936 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block125 : ∀ m : Fin 64,
    forwardTable0 (8000 + m.val) < 2^112 ∧ backwardTable0 (8000 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block126 : ∀ m : Fin 64,
    forwardTable0 (8064 + m.val) < 2^112 ∧ backwardTable0 (8064 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds0_block127 : ∀ m : Fin 64,
    forwardTable0 (8128 + m.val) < 2^112 ∧ backwardTable0 (8128 + m.val) < 2^112 := by
  decide +kernel

theorem bounds0 (m : Fin 8192) :
    forwardTable0 m.val < 2^112 ∧ backwardTable0 m.val < 2^112 := by
  apply check_blocks (P := fun a => forwardTable0 a < 2^112 ∧ backwardTable0 a < 2^112)
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact bounds0_block0
  · exact bounds0_block1
  · exact bounds0_block2
  · exact bounds0_block3
  · exact bounds0_block4
  · exact bounds0_block5
  · exact bounds0_block6
  · exact bounds0_block7
  · exact bounds0_block8
  · exact bounds0_block9
  · exact bounds0_block10
  · exact bounds0_block11
  · exact bounds0_block12
  · exact bounds0_block13
  · exact bounds0_block14
  · exact bounds0_block15
  · exact bounds0_block16
  · exact bounds0_block17
  · exact bounds0_block18
  · exact bounds0_block19
  · exact bounds0_block20
  · exact bounds0_block21
  · exact bounds0_block22
  · exact bounds0_block23
  · exact bounds0_block24
  · exact bounds0_block25
  · exact bounds0_block26
  · exact bounds0_block27
  · exact bounds0_block28
  · exact bounds0_block29
  · exact bounds0_block30
  · exact bounds0_block31
  · exact bounds0_block32
  · exact bounds0_block33
  · exact bounds0_block34
  · exact bounds0_block35
  · exact bounds0_block36
  · exact bounds0_block37
  · exact bounds0_block38
  · exact bounds0_block39
  · exact bounds0_block40
  · exact bounds0_block41
  · exact bounds0_block42
  · exact bounds0_block43
  · exact bounds0_block44
  · exact bounds0_block45
  · exact bounds0_block46
  · exact bounds0_block47
  · exact bounds0_block48
  · exact bounds0_block49
  · exact bounds0_block50
  · exact bounds0_block51
  · exact bounds0_block52
  · exact bounds0_block53
  · exact bounds0_block54
  · exact bounds0_block55
  · exact bounds0_block56
  · exact bounds0_block57
  · exact bounds0_block58
  · exact bounds0_block59
  · exact bounds0_block60
  · exact bounds0_block61
  · exact bounds0_block62
  · exact bounds0_block63
  · exact bounds0_block64
  · exact bounds0_block65
  · exact bounds0_block66
  · exact bounds0_block67
  · exact bounds0_block68
  · exact bounds0_block69
  · exact bounds0_block70
  · exact bounds0_block71
  · exact bounds0_block72
  · exact bounds0_block73
  · exact bounds0_block74
  · exact bounds0_block75
  · exact bounds0_block76
  · exact bounds0_block77
  · exact bounds0_block78
  · exact bounds0_block79
  · exact bounds0_block80
  · exact bounds0_block81
  · exact bounds0_block82
  · exact bounds0_block83
  · exact bounds0_block84
  · exact bounds0_block85
  · exact bounds0_block86
  · exact bounds0_block87
  · exact bounds0_block88
  · exact bounds0_block89
  · exact bounds0_block90
  · exact bounds0_block91
  · exact bounds0_block92
  · exact bounds0_block93
  · exact bounds0_block94
  · exact bounds0_block95
  · exact bounds0_block96
  · exact bounds0_block97
  · exact bounds0_block98
  · exact bounds0_block99
  · exact bounds0_block100
  · exact bounds0_block101
  · exact bounds0_block102
  · exact bounds0_block103
  · exact bounds0_block104
  · exact bounds0_block105
  · exact bounds0_block106
  · exact bounds0_block107
  · exact bounds0_block108
  · exact bounds0_block109
  · exact bounds0_block110
  · exact bounds0_block111
  · exact bounds0_block112
  · exact bounds0_block113
  · exact bounds0_block114
  · exact bounds0_block115
  · exact bounds0_block116
  · exact bounds0_block117
  · exact bounds0_block118
  · exact bounds0_block119
  · exact bounds0_block120
  · exact bounds0_block121
  · exact bounds0_block122
  · exact bounds0_block123
  · exact bounds0_block124
  · exact bounds0_block125
  · exact bounds0_block126
  · exact bounds0_block127

set_option maxRecDepth 10000 in
private theorem matches0_block0 : ∀ m : Fin 64,
    (forwardTable0 (0 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (0 + m.val))).val → Listed 0 (0 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block1 : ∀ m : Fin 64,
    (forwardTable0 (64 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (64 + m.val))).val → Listed 0 (64 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block2 : ∀ m : Fin 64,
    (forwardTable0 (128 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (128 + m.val))).val → Listed 0 (128 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block3 : ∀ m : Fin 64,
    (forwardTable0 (192 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (192 + m.val))).val → Listed 0 (192 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block4 : ∀ m : Fin 64,
    (forwardTable0 (256 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (256 + m.val))).val → Listed 0 (256 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block5 : ∀ m : Fin 64,
    (forwardTable0 (320 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (320 + m.val))).val → Listed 0 (320 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block6 : ∀ m : Fin 64,
    (forwardTable0 (384 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (384 + m.val))).val → Listed 0 (384 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block7 : ∀ m : Fin 64,
    (forwardTable0 (448 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (448 + m.val))).val → Listed 0 (448 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block8 : ∀ m : Fin 64,
    (forwardTable0 (512 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (512 + m.val))).val → Listed 0 (512 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block9 : ∀ m : Fin 64,
    (forwardTable0 (576 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (576 + m.val))).val → Listed 0 (576 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block10 : ∀ m : Fin 64,
    (forwardTable0 (640 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (640 + m.val))).val → Listed 0 (640 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block11 : ∀ m : Fin 64,
    (forwardTable0 (704 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (704 + m.val))).val → Listed 0 (704 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block12 : ∀ m : Fin 64,
    (forwardTable0 (768 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (768 + m.val))).val → Listed 0 (768 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block13 : ∀ m : Fin 64,
    (forwardTable0 (832 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (832 + m.val))).val → Listed 0 (832 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block14 : ∀ m : Fin 64,
    (forwardTable0 (896 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (896 + m.val))).val → Listed 0 (896 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block15 : ∀ m : Fin 64,
    (forwardTable0 (960 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (960 + m.val))).val → Listed 0 (960 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block16 : ∀ m : Fin 64,
    (forwardTable0 (1024 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1024 + m.val))).val → Listed 0 (1024 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block17 : ∀ m : Fin 64,
    (forwardTable0 (1088 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1088 + m.val))).val → Listed 0 (1088 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block18 : ∀ m : Fin 64,
    (forwardTable0 (1152 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1152 + m.val))).val → Listed 0 (1152 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block19 : ∀ m : Fin 64,
    (forwardTable0 (1216 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1216 + m.val))).val → Listed 0 (1216 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block20 : ∀ m : Fin 64,
    (forwardTable0 (1280 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1280 + m.val))).val → Listed 0 (1280 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block21 : ∀ m : Fin 64,
    (forwardTable0 (1344 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1344 + m.val))).val → Listed 0 (1344 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block22 : ∀ m : Fin 64,
    (forwardTable0 (1408 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1408 + m.val))).val → Listed 0 (1408 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block23 : ∀ m : Fin 64,
    (forwardTable0 (1472 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1472 + m.val))).val → Listed 0 (1472 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block24 : ∀ m : Fin 64,
    (forwardTable0 (1536 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1536 + m.val))).val → Listed 0 (1536 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block25 : ∀ m : Fin 64,
    (forwardTable0 (1600 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1600 + m.val))).val → Listed 0 (1600 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block26 : ∀ m : Fin 64,
    (forwardTable0 (1664 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1664 + m.val))).val → Listed 0 (1664 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block27 : ∀ m : Fin 64,
    (forwardTable0 (1728 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1728 + m.val))).val → Listed 0 (1728 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block28 : ∀ m : Fin 64,
    (forwardTable0 (1792 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1792 + m.val))).val → Listed 0 (1792 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block29 : ∀ m : Fin 64,
    (forwardTable0 (1856 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1856 + m.val))).val → Listed 0 (1856 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block30 : ∀ m : Fin 64,
    (forwardTable0 (1920 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1920 + m.val))).val → Listed 0 (1920 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block31 : ∀ m : Fin 64,
    (forwardTable0 (1984 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (1984 + m.val))).val → Listed 0 (1984 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block32 : ∀ m : Fin 64,
    (forwardTable0 (2048 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2048 + m.val))).val → Listed 0 (2048 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block33 : ∀ m : Fin 64,
    (forwardTable0 (2112 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2112 + m.val))).val → Listed 0 (2112 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block34 : ∀ m : Fin 64,
    (forwardTable0 (2176 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2176 + m.val))).val → Listed 0 (2176 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block35 : ∀ m : Fin 64,
    (forwardTable0 (2240 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2240 + m.val))).val → Listed 0 (2240 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block36 : ∀ m : Fin 64,
    (forwardTable0 (2304 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2304 + m.val))).val → Listed 0 (2304 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block37 : ∀ m : Fin 64,
    (forwardTable0 (2368 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2368 + m.val))).val → Listed 0 (2368 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block38 : ∀ m : Fin 64,
    (forwardTable0 (2432 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2432 + m.val))).val → Listed 0 (2432 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block39 : ∀ m : Fin 64,
    (forwardTable0 (2496 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2496 + m.val))).val → Listed 0 (2496 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block40 : ∀ m : Fin 64,
    (forwardTable0 (2560 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2560 + m.val))).val → Listed 0 (2560 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block41 : ∀ m : Fin 64,
    (forwardTable0 (2624 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2624 + m.val))).val → Listed 0 (2624 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block42 : ∀ m : Fin 64,
    (forwardTable0 (2688 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2688 + m.val))).val → Listed 0 (2688 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block43 : ∀ m : Fin 64,
    (forwardTable0 (2752 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2752 + m.val))).val → Listed 0 (2752 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block44 : ∀ m : Fin 64,
    (forwardTable0 (2816 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2816 + m.val))).val → Listed 0 (2816 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block45 : ∀ m : Fin 64,
    (forwardTable0 (2880 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2880 + m.val))).val → Listed 0 (2880 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block46 : ∀ m : Fin 64,
    (forwardTable0 (2944 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (2944 + m.val))).val → Listed 0 (2944 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block47 : ∀ m : Fin 64,
    (forwardTable0 (3008 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3008 + m.val))).val → Listed 0 (3008 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block48 : ∀ m : Fin 64,
    (forwardTable0 (3072 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3072 + m.val))).val → Listed 0 (3072 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block49 : ∀ m : Fin 64,
    (forwardTable0 (3136 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3136 + m.val))).val → Listed 0 (3136 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block50 : ∀ m : Fin 64,
    (forwardTable0 (3200 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3200 + m.val))).val → Listed 0 (3200 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block51 : ∀ m : Fin 64,
    (forwardTable0 (3264 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3264 + m.val))).val → Listed 0 (3264 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block52 : ∀ m : Fin 64,
    (forwardTable0 (3328 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3328 + m.val))).val → Listed 0 (3328 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block53 : ∀ m : Fin 64,
    (forwardTable0 (3392 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3392 + m.val))).val → Listed 0 (3392 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block54 : ∀ m : Fin 64,
    (forwardTable0 (3456 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3456 + m.val))).val → Listed 0 (3456 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block55 : ∀ m : Fin 64,
    (forwardTable0 (3520 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3520 + m.val))).val → Listed 0 (3520 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block56 : ∀ m : Fin 64,
    (forwardTable0 (3584 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3584 + m.val))).val → Listed 0 (3584 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block57 : ∀ m : Fin 64,
    (forwardTable0 (3648 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3648 + m.val))).val → Listed 0 (3648 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block58 : ∀ m : Fin 64,
    (forwardTable0 (3712 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3712 + m.val))).val → Listed 0 (3712 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block59 : ∀ m : Fin 64,
    (forwardTable0 (3776 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3776 + m.val))).val → Listed 0 (3776 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block60 : ∀ m : Fin 64,
    (forwardTable0 (3840 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3840 + m.val))).val → Listed 0 (3840 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block61 : ∀ m : Fin 64,
    (forwardTable0 (3904 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3904 + m.val))).val → Listed 0 (3904 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block62 : ∀ m : Fin 64,
    (forwardTable0 (3968 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (3968 + m.val))).val → Listed 0 (3968 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block63 : ∀ m : Fin 64,
    (forwardTable0 (4032 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4032 + m.val))).val → Listed 0 (4032 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block64 : ∀ m : Fin 64,
    (forwardTable0 (4096 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4096 + m.val))).val → Listed 0 (4096 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block65 : ∀ m : Fin 64,
    (forwardTable0 (4160 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4160 + m.val))).val → Listed 0 (4160 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block66 : ∀ m : Fin 64,
    (forwardTable0 (4224 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4224 + m.val))).val → Listed 0 (4224 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block67 : ∀ m : Fin 64,
    (forwardTable0 (4288 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4288 + m.val))).val → Listed 0 (4288 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block68 : ∀ m : Fin 64,
    (forwardTable0 (4352 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4352 + m.val))).val → Listed 0 (4352 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block69 : ∀ m : Fin 64,
    (forwardTable0 (4416 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4416 + m.val))).val → Listed 0 (4416 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block70 : ∀ m : Fin 64,
    (forwardTable0 (4480 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4480 + m.val))).val → Listed 0 (4480 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block71 : ∀ m : Fin 64,
    (forwardTable0 (4544 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4544 + m.val))).val → Listed 0 (4544 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block72 : ∀ m : Fin 64,
    (forwardTable0 (4608 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4608 + m.val))).val → Listed 0 (4608 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block73 : ∀ m : Fin 64,
    (forwardTable0 (4672 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4672 + m.val))).val → Listed 0 (4672 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block74 : ∀ m : Fin 64,
    (forwardTable0 (4736 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4736 + m.val))).val → Listed 0 (4736 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block75 : ∀ m : Fin 64,
    (forwardTable0 (4800 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4800 + m.val))).val → Listed 0 (4800 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block76 : ∀ m : Fin 64,
    (forwardTable0 (4864 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4864 + m.val))).val → Listed 0 (4864 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block77 : ∀ m : Fin 64,
    (forwardTable0 (4928 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4928 + m.val))).val → Listed 0 (4928 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block78 : ∀ m : Fin 64,
    (forwardTable0 (4992 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (4992 + m.val))).val → Listed 0 (4992 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block79 : ∀ m : Fin 64,
    (forwardTable0 (5056 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5056 + m.val))).val → Listed 0 (5056 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block80 : ∀ m : Fin 64,
    (forwardTable0 (5120 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5120 + m.val))).val → Listed 0 (5120 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block81 : ∀ m : Fin 64,
    (forwardTable0 (5184 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5184 + m.val))).val → Listed 0 (5184 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block82 : ∀ m : Fin 64,
    (forwardTable0 (5248 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5248 + m.val))).val → Listed 0 (5248 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block83 : ∀ m : Fin 64,
    (forwardTable0 (5312 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5312 + m.val))).val → Listed 0 (5312 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block84 : ∀ m : Fin 64,
    (forwardTable0 (5376 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5376 + m.val))).val → Listed 0 (5376 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block85 : ∀ m : Fin 64,
    (forwardTable0 (5440 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5440 + m.val))).val → Listed 0 (5440 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block86 : ∀ m : Fin 64,
    (forwardTable0 (5504 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5504 + m.val))).val → Listed 0 (5504 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block87 : ∀ m : Fin 64,
    (forwardTable0 (5568 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5568 + m.val))).val → Listed 0 (5568 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block88 : ∀ m : Fin 64,
    (forwardTable0 (5632 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5632 + m.val))).val → Listed 0 (5632 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block89 : ∀ m : Fin 64,
    (forwardTable0 (5696 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5696 + m.val))).val → Listed 0 (5696 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block90 : ∀ m : Fin 64,
    (forwardTable0 (5760 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5760 + m.val))).val → Listed 0 (5760 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block91 : ∀ m : Fin 64,
    (forwardTable0 (5824 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5824 + m.val))).val → Listed 0 (5824 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block92 : ∀ m : Fin 64,
    (forwardTable0 (5888 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5888 + m.val))).val → Listed 0 (5888 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block93 : ∀ m : Fin 64,
    (forwardTable0 (5952 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (5952 + m.val))).val → Listed 0 (5952 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block94 : ∀ m : Fin 64,
    (forwardTable0 (6016 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6016 + m.val))).val → Listed 0 (6016 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block95 : ∀ m : Fin 64,
    (forwardTable0 (6080 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6080 + m.val))).val → Listed 0 (6080 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block96 : ∀ m : Fin 64,
    (forwardTable0 (6144 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6144 + m.val))).val → Listed 0 (6144 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block97 : ∀ m : Fin 64,
    (forwardTable0 (6208 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6208 + m.val))).val → Listed 0 (6208 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block98 : ∀ m : Fin 64,
    (forwardTable0 (6272 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6272 + m.val))).val → Listed 0 (6272 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block99 : ∀ m : Fin 64,
    (forwardTable0 (6336 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6336 + m.val))).val → Listed 0 (6336 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block100 : ∀ m : Fin 64,
    (forwardTable0 (6400 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6400 + m.val))).val → Listed 0 (6400 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block101 : ∀ m : Fin 64,
    (forwardTable0 (6464 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6464 + m.val))).val → Listed 0 (6464 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block102 : ∀ m : Fin 64,
    (forwardTable0 (6528 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6528 + m.val))).val → Listed 0 (6528 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block103 : ∀ m : Fin 64,
    (forwardTable0 (6592 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6592 + m.val))).val → Listed 0 (6592 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block104 : ∀ m : Fin 64,
    (forwardTable0 (6656 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6656 + m.val))).val → Listed 0 (6656 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block105 : ∀ m : Fin 64,
    (forwardTable0 (6720 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6720 + m.val))).val → Listed 0 (6720 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block106 : ∀ m : Fin 64,
    (forwardTable0 (6784 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6784 + m.val))).val → Listed 0 (6784 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block107 : ∀ m : Fin 64,
    (forwardTable0 (6848 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6848 + m.val))).val → Listed 0 (6848 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block108 : ∀ m : Fin 64,
    (forwardTable0 (6912 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6912 + m.val))).val → Listed 0 (6912 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block109 : ∀ m : Fin 64,
    (forwardTable0 (6976 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (6976 + m.val))).val → Listed 0 (6976 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block110 : ∀ m : Fin 64,
    (forwardTable0 (7040 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7040 + m.val))).val → Listed 0 (7040 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block111 : ∀ m : Fin 64,
    (forwardTable0 (7104 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7104 + m.val))).val → Listed 0 (7104 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block112 : ∀ m : Fin 64,
    (forwardTable0 (7168 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7168 + m.val))).val → Listed 0 (7168 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block113 : ∀ m : Fin 64,
    (forwardTable0 (7232 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7232 + m.val))).val → Listed 0 (7232 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block114 : ∀ m : Fin 64,
    (forwardTable0 (7296 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7296 + m.val))).val → Listed 0 (7296 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block115 : ∀ m : Fin 64,
    (forwardTable0 (7360 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7360 + m.val))).val → Listed 0 (7360 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block116 : ∀ m : Fin 64,
    (forwardTable0 (7424 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7424 + m.val))).val → Listed 0 (7424 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block117 : ∀ m : Fin 64,
    (forwardTable0 (7488 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7488 + m.val))).val → Listed 0 (7488 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block118 : ∀ m : Fin 64,
    (forwardTable0 (7552 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7552 + m.val))).val → Listed 0 (7552 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block119 : ∀ m : Fin 64,
    (forwardTable0 (7616 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7616 + m.val))).val → Listed 0 (7616 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block120 : ∀ m : Fin 64,
    (forwardTable0 (7680 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7680 + m.val))).val → Listed 0 (7680 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block121 : ∀ m : Fin 64,
    (forwardTable0 (7744 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7744 + m.val))).val → Listed 0 (7744 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block122 : ∀ m : Fin 64,
    (forwardTable0 (7808 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7808 + m.val))).val → Listed 0 (7808 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block123 : ∀ m : Fin 64,
    (forwardTable0 (7872 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7872 + m.val))).val → Listed 0 (7872 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block124 : ∀ m : Fin 64,
    (forwardTable0 (7936 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (7936 + m.val))).val → Listed 0 (7936 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block125 : ∀ m : Fin 64,
    (forwardTable0 (8000 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (8000 + m.val))).val → Listed 0 (8000 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block126 : ∀ m : Fin 64,
    (forwardTable0 (8064 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (8064 + m.val))).val → Listed 0 (8064 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches0_block127 : ∀ m : Fin 64,
    (forwardTable0 (8128 + m.val) = backwardTable0 (reverseCode (Fin.ofNat 8192 (8128 + m.val))).val → Listed 0 (8128 + m.val)) := by
  decide +kernel

theorem matches0 (m : Fin 8192) :
    (forwardTable0 m.val = backwardTable0 (reverseCode (Fin.ofNat 8192 m.val)).val → Listed 0 m.val) := by
  apply check_blocks (P := fun a => (forwardTable0 a = backwardTable0 (reverseCode (Fin.ofNat 8192 a)).val → Listed 0 a))
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact matches0_block0
  · exact matches0_block1
  · exact matches0_block2
  · exact matches0_block3
  · exact matches0_block4
  · exact matches0_block5
  · exact matches0_block6
  · exact matches0_block7
  · exact matches0_block8
  · exact matches0_block9
  · exact matches0_block10
  · exact matches0_block11
  · exact matches0_block12
  · exact matches0_block13
  · exact matches0_block14
  · exact matches0_block15
  · exact matches0_block16
  · exact matches0_block17
  · exact matches0_block18
  · exact matches0_block19
  · exact matches0_block20
  · exact matches0_block21
  · exact matches0_block22
  · exact matches0_block23
  · exact matches0_block24
  · exact matches0_block25
  · exact matches0_block26
  · exact matches0_block27
  · exact matches0_block28
  · exact matches0_block29
  · exact matches0_block30
  · exact matches0_block31
  · exact matches0_block32
  · exact matches0_block33
  · exact matches0_block34
  · exact matches0_block35
  · exact matches0_block36
  · exact matches0_block37
  · exact matches0_block38
  · exact matches0_block39
  · exact matches0_block40
  · exact matches0_block41
  · exact matches0_block42
  · exact matches0_block43
  · exact matches0_block44
  · exact matches0_block45
  · exact matches0_block46
  · exact matches0_block47
  · exact matches0_block48
  · exact matches0_block49
  · exact matches0_block50
  · exact matches0_block51
  · exact matches0_block52
  · exact matches0_block53
  · exact matches0_block54
  · exact matches0_block55
  · exact matches0_block56
  · exact matches0_block57
  · exact matches0_block58
  · exact matches0_block59
  · exact matches0_block60
  · exact matches0_block61
  · exact matches0_block62
  · exact matches0_block63
  · exact matches0_block64
  · exact matches0_block65
  · exact matches0_block66
  · exact matches0_block67
  · exact matches0_block68
  · exact matches0_block69
  · exact matches0_block70
  · exact matches0_block71
  · exact matches0_block72
  · exact matches0_block73
  · exact matches0_block74
  · exact matches0_block75
  · exact matches0_block76
  · exact matches0_block77
  · exact matches0_block78
  · exact matches0_block79
  · exact matches0_block80
  · exact matches0_block81
  · exact matches0_block82
  · exact matches0_block83
  · exact matches0_block84
  · exact matches0_block85
  · exact matches0_block86
  · exact matches0_block87
  · exact matches0_block88
  · exact matches0_block89
  · exact matches0_block90
  · exact matches0_block91
  · exact matches0_block92
  · exact matches0_block93
  · exact matches0_block94
  · exact matches0_block95
  · exact matches0_block96
  · exact matches0_block97
  · exact matches0_block98
  · exact matches0_block99
  · exact matches0_block100
  · exact matches0_block101
  · exact matches0_block102
  · exact matches0_block103
  · exact matches0_block104
  · exact matches0_block105
  · exact matches0_block106
  · exact matches0_block107
  · exact matches0_block108
  · exact matches0_block109
  · exact matches0_block110
  · exact matches0_block111
  · exact matches0_block112
  · exact matches0_block113
  · exact matches0_block114
  · exact matches0_block115
  · exact matches0_block116
  · exact matches0_block117
  · exact matches0_block118
  · exact matches0_block119
  · exact matches0_block120
  · exact matches0_block121
  · exact matches0_block122
  · exact matches0_block123
  · exact matches0_block124
  · exact matches0_block125
  · exact matches0_block126
  · exact matches0_block127


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
