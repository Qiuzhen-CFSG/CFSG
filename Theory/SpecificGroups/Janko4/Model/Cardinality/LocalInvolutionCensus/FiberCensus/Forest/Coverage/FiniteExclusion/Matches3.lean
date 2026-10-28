module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Witnesses

/-!
# Bounds and mask witnesses for fiber 3

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
theorem backward_zero3 : backwardTable3 0 = liftEntry 3 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block0 : ∀ m : Fin 64,
    forwardTable3 (0 + m.val) < 2^112 ∧ backwardTable3 (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block1 : ∀ m : Fin 64,
    forwardTable3 (64 + m.val) < 2^112 ∧ backwardTable3 (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block2 : ∀ m : Fin 64,
    forwardTable3 (128 + m.val) < 2^112 ∧ backwardTable3 (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block3 : ∀ m : Fin 64,
    forwardTable3 (192 + m.val) < 2^112 ∧ backwardTable3 (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block4 : ∀ m : Fin 64,
    forwardTable3 (256 + m.val) < 2^112 ∧ backwardTable3 (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block5 : ∀ m : Fin 64,
    forwardTable3 (320 + m.val) < 2^112 ∧ backwardTable3 (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block6 : ∀ m : Fin 64,
    forwardTable3 (384 + m.val) < 2^112 ∧ backwardTable3 (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block7 : ∀ m : Fin 64,
    forwardTable3 (448 + m.val) < 2^112 ∧ backwardTable3 (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block8 : ∀ m : Fin 64,
    forwardTable3 (512 + m.val) < 2^112 ∧ backwardTable3 (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block9 : ∀ m : Fin 64,
    forwardTable3 (576 + m.val) < 2^112 ∧ backwardTable3 (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block10 : ∀ m : Fin 64,
    forwardTable3 (640 + m.val) < 2^112 ∧ backwardTable3 (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block11 : ∀ m : Fin 64,
    forwardTable3 (704 + m.val) < 2^112 ∧ backwardTable3 (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block12 : ∀ m : Fin 64,
    forwardTable3 (768 + m.val) < 2^112 ∧ backwardTable3 (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block13 : ∀ m : Fin 64,
    forwardTable3 (832 + m.val) < 2^112 ∧ backwardTable3 (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block14 : ∀ m : Fin 64,
    forwardTable3 (896 + m.val) < 2^112 ∧ backwardTable3 (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block15 : ∀ m : Fin 64,
    forwardTable3 (960 + m.val) < 2^112 ∧ backwardTable3 (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block16 : ∀ m : Fin 64,
    forwardTable3 (1024 + m.val) < 2^112 ∧ backwardTable3 (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block17 : ∀ m : Fin 64,
    forwardTable3 (1088 + m.val) < 2^112 ∧ backwardTable3 (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block18 : ∀ m : Fin 64,
    forwardTable3 (1152 + m.val) < 2^112 ∧ backwardTable3 (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block19 : ∀ m : Fin 64,
    forwardTable3 (1216 + m.val) < 2^112 ∧ backwardTable3 (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block20 : ∀ m : Fin 64,
    forwardTable3 (1280 + m.val) < 2^112 ∧ backwardTable3 (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block21 : ∀ m : Fin 64,
    forwardTable3 (1344 + m.val) < 2^112 ∧ backwardTable3 (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block22 : ∀ m : Fin 64,
    forwardTable3 (1408 + m.val) < 2^112 ∧ backwardTable3 (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block23 : ∀ m : Fin 64,
    forwardTable3 (1472 + m.val) < 2^112 ∧ backwardTable3 (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block24 : ∀ m : Fin 64,
    forwardTable3 (1536 + m.val) < 2^112 ∧ backwardTable3 (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block25 : ∀ m : Fin 64,
    forwardTable3 (1600 + m.val) < 2^112 ∧ backwardTable3 (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block26 : ∀ m : Fin 64,
    forwardTable3 (1664 + m.val) < 2^112 ∧ backwardTable3 (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block27 : ∀ m : Fin 64,
    forwardTable3 (1728 + m.val) < 2^112 ∧ backwardTable3 (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block28 : ∀ m : Fin 64,
    forwardTable3 (1792 + m.val) < 2^112 ∧ backwardTable3 (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block29 : ∀ m : Fin 64,
    forwardTable3 (1856 + m.val) < 2^112 ∧ backwardTable3 (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block30 : ∀ m : Fin 64,
    forwardTable3 (1920 + m.val) < 2^112 ∧ backwardTable3 (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block31 : ∀ m : Fin 64,
    forwardTable3 (1984 + m.val) < 2^112 ∧ backwardTable3 (1984 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block32 : ∀ m : Fin 64,
    forwardTable3 (2048 + m.val) < 2^112 ∧ backwardTable3 (2048 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block33 : ∀ m : Fin 64,
    forwardTable3 (2112 + m.val) < 2^112 ∧ backwardTable3 (2112 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block34 : ∀ m : Fin 64,
    forwardTable3 (2176 + m.val) < 2^112 ∧ backwardTable3 (2176 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block35 : ∀ m : Fin 64,
    forwardTable3 (2240 + m.val) < 2^112 ∧ backwardTable3 (2240 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block36 : ∀ m : Fin 64,
    forwardTable3 (2304 + m.val) < 2^112 ∧ backwardTable3 (2304 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block37 : ∀ m : Fin 64,
    forwardTable3 (2368 + m.val) < 2^112 ∧ backwardTable3 (2368 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block38 : ∀ m : Fin 64,
    forwardTable3 (2432 + m.val) < 2^112 ∧ backwardTable3 (2432 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block39 : ∀ m : Fin 64,
    forwardTable3 (2496 + m.val) < 2^112 ∧ backwardTable3 (2496 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block40 : ∀ m : Fin 64,
    forwardTable3 (2560 + m.val) < 2^112 ∧ backwardTable3 (2560 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block41 : ∀ m : Fin 64,
    forwardTable3 (2624 + m.val) < 2^112 ∧ backwardTable3 (2624 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block42 : ∀ m : Fin 64,
    forwardTable3 (2688 + m.val) < 2^112 ∧ backwardTable3 (2688 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block43 : ∀ m : Fin 64,
    forwardTable3 (2752 + m.val) < 2^112 ∧ backwardTable3 (2752 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block44 : ∀ m : Fin 64,
    forwardTable3 (2816 + m.val) < 2^112 ∧ backwardTable3 (2816 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block45 : ∀ m : Fin 64,
    forwardTable3 (2880 + m.val) < 2^112 ∧ backwardTable3 (2880 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block46 : ∀ m : Fin 64,
    forwardTable3 (2944 + m.val) < 2^112 ∧ backwardTable3 (2944 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block47 : ∀ m : Fin 64,
    forwardTable3 (3008 + m.val) < 2^112 ∧ backwardTable3 (3008 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block48 : ∀ m : Fin 64,
    forwardTable3 (3072 + m.val) < 2^112 ∧ backwardTable3 (3072 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block49 : ∀ m : Fin 64,
    forwardTable3 (3136 + m.val) < 2^112 ∧ backwardTable3 (3136 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block50 : ∀ m : Fin 64,
    forwardTable3 (3200 + m.val) < 2^112 ∧ backwardTable3 (3200 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block51 : ∀ m : Fin 64,
    forwardTable3 (3264 + m.val) < 2^112 ∧ backwardTable3 (3264 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block52 : ∀ m : Fin 64,
    forwardTable3 (3328 + m.val) < 2^112 ∧ backwardTable3 (3328 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block53 : ∀ m : Fin 64,
    forwardTable3 (3392 + m.val) < 2^112 ∧ backwardTable3 (3392 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block54 : ∀ m : Fin 64,
    forwardTable3 (3456 + m.val) < 2^112 ∧ backwardTable3 (3456 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block55 : ∀ m : Fin 64,
    forwardTable3 (3520 + m.val) < 2^112 ∧ backwardTable3 (3520 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block56 : ∀ m : Fin 64,
    forwardTable3 (3584 + m.val) < 2^112 ∧ backwardTable3 (3584 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block57 : ∀ m : Fin 64,
    forwardTable3 (3648 + m.val) < 2^112 ∧ backwardTable3 (3648 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block58 : ∀ m : Fin 64,
    forwardTable3 (3712 + m.val) < 2^112 ∧ backwardTable3 (3712 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block59 : ∀ m : Fin 64,
    forwardTable3 (3776 + m.val) < 2^112 ∧ backwardTable3 (3776 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block60 : ∀ m : Fin 64,
    forwardTable3 (3840 + m.val) < 2^112 ∧ backwardTable3 (3840 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block61 : ∀ m : Fin 64,
    forwardTable3 (3904 + m.val) < 2^112 ∧ backwardTable3 (3904 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block62 : ∀ m : Fin 64,
    forwardTable3 (3968 + m.val) < 2^112 ∧ backwardTable3 (3968 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block63 : ∀ m : Fin 64,
    forwardTable3 (4032 + m.val) < 2^112 ∧ backwardTable3 (4032 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block64 : ∀ m : Fin 64,
    forwardTable3 (4096 + m.val) < 2^112 ∧ backwardTable3 (4096 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block65 : ∀ m : Fin 64,
    forwardTable3 (4160 + m.val) < 2^112 ∧ backwardTable3 (4160 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block66 : ∀ m : Fin 64,
    forwardTable3 (4224 + m.val) < 2^112 ∧ backwardTable3 (4224 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block67 : ∀ m : Fin 64,
    forwardTable3 (4288 + m.val) < 2^112 ∧ backwardTable3 (4288 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block68 : ∀ m : Fin 64,
    forwardTable3 (4352 + m.val) < 2^112 ∧ backwardTable3 (4352 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block69 : ∀ m : Fin 64,
    forwardTable3 (4416 + m.val) < 2^112 ∧ backwardTable3 (4416 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block70 : ∀ m : Fin 64,
    forwardTable3 (4480 + m.val) < 2^112 ∧ backwardTable3 (4480 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block71 : ∀ m : Fin 64,
    forwardTable3 (4544 + m.val) < 2^112 ∧ backwardTable3 (4544 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block72 : ∀ m : Fin 64,
    forwardTable3 (4608 + m.val) < 2^112 ∧ backwardTable3 (4608 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block73 : ∀ m : Fin 64,
    forwardTable3 (4672 + m.val) < 2^112 ∧ backwardTable3 (4672 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block74 : ∀ m : Fin 64,
    forwardTable3 (4736 + m.val) < 2^112 ∧ backwardTable3 (4736 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block75 : ∀ m : Fin 64,
    forwardTable3 (4800 + m.val) < 2^112 ∧ backwardTable3 (4800 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block76 : ∀ m : Fin 64,
    forwardTable3 (4864 + m.val) < 2^112 ∧ backwardTable3 (4864 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block77 : ∀ m : Fin 64,
    forwardTable3 (4928 + m.val) < 2^112 ∧ backwardTable3 (4928 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block78 : ∀ m : Fin 64,
    forwardTable3 (4992 + m.val) < 2^112 ∧ backwardTable3 (4992 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block79 : ∀ m : Fin 64,
    forwardTable3 (5056 + m.val) < 2^112 ∧ backwardTable3 (5056 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block80 : ∀ m : Fin 64,
    forwardTable3 (5120 + m.val) < 2^112 ∧ backwardTable3 (5120 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block81 : ∀ m : Fin 64,
    forwardTable3 (5184 + m.val) < 2^112 ∧ backwardTable3 (5184 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block82 : ∀ m : Fin 64,
    forwardTable3 (5248 + m.val) < 2^112 ∧ backwardTable3 (5248 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block83 : ∀ m : Fin 64,
    forwardTable3 (5312 + m.val) < 2^112 ∧ backwardTable3 (5312 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block84 : ∀ m : Fin 64,
    forwardTable3 (5376 + m.val) < 2^112 ∧ backwardTable3 (5376 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block85 : ∀ m : Fin 64,
    forwardTable3 (5440 + m.val) < 2^112 ∧ backwardTable3 (5440 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block86 : ∀ m : Fin 64,
    forwardTable3 (5504 + m.val) < 2^112 ∧ backwardTable3 (5504 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block87 : ∀ m : Fin 64,
    forwardTable3 (5568 + m.val) < 2^112 ∧ backwardTable3 (5568 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block88 : ∀ m : Fin 64,
    forwardTable3 (5632 + m.val) < 2^112 ∧ backwardTable3 (5632 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block89 : ∀ m : Fin 64,
    forwardTable3 (5696 + m.val) < 2^112 ∧ backwardTable3 (5696 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block90 : ∀ m : Fin 64,
    forwardTable3 (5760 + m.val) < 2^112 ∧ backwardTable3 (5760 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block91 : ∀ m : Fin 64,
    forwardTable3 (5824 + m.val) < 2^112 ∧ backwardTable3 (5824 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block92 : ∀ m : Fin 64,
    forwardTable3 (5888 + m.val) < 2^112 ∧ backwardTable3 (5888 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block93 : ∀ m : Fin 64,
    forwardTable3 (5952 + m.val) < 2^112 ∧ backwardTable3 (5952 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block94 : ∀ m : Fin 64,
    forwardTable3 (6016 + m.val) < 2^112 ∧ backwardTable3 (6016 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block95 : ∀ m : Fin 64,
    forwardTable3 (6080 + m.val) < 2^112 ∧ backwardTable3 (6080 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block96 : ∀ m : Fin 64,
    forwardTable3 (6144 + m.val) < 2^112 ∧ backwardTable3 (6144 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block97 : ∀ m : Fin 64,
    forwardTable3 (6208 + m.val) < 2^112 ∧ backwardTable3 (6208 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block98 : ∀ m : Fin 64,
    forwardTable3 (6272 + m.val) < 2^112 ∧ backwardTable3 (6272 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block99 : ∀ m : Fin 64,
    forwardTable3 (6336 + m.val) < 2^112 ∧ backwardTable3 (6336 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block100 : ∀ m : Fin 64,
    forwardTable3 (6400 + m.val) < 2^112 ∧ backwardTable3 (6400 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block101 : ∀ m : Fin 64,
    forwardTable3 (6464 + m.val) < 2^112 ∧ backwardTable3 (6464 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block102 : ∀ m : Fin 64,
    forwardTable3 (6528 + m.val) < 2^112 ∧ backwardTable3 (6528 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block103 : ∀ m : Fin 64,
    forwardTable3 (6592 + m.val) < 2^112 ∧ backwardTable3 (6592 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block104 : ∀ m : Fin 64,
    forwardTable3 (6656 + m.val) < 2^112 ∧ backwardTable3 (6656 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block105 : ∀ m : Fin 64,
    forwardTable3 (6720 + m.val) < 2^112 ∧ backwardTable3 (6720 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block106 : ∀ m : Fin 64,
    forwardTable3 (6784 + m.val) < 2^112 ∧ backwardTable3 (6784 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block107 : ∀ m : Fin 64,
    forwardTable3 (6848 + m.val) < 2^112 ∧ backwardTable3 (6848 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block108 : ∀ m : Fin 64,
    forwardTable3 (6912 + m.val) < 2^112 ∧ backwardTable3 (6912 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block109 : ∀ m : Fin 64,
    forwardTable3 (6976 + m.val) < 2^112 ∧ backwardTable3 (6976 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block110 : ∀ m : Fin 64,
    forwardTable3 (7040 + m.val) < 2^112 ∧ backwardTable3 (7040 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block111 : ∀ m : Fin 64,
    forwardTable3 (7104 + m.val) < 2^112 ∧ backwardTable3 (7104 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block112 : ∀ m : Fin 64,
    forwardTable3 (7168 + m.val) < 2^112 ∧ backwardTable3 (7168 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block113 : ∀ m : Fin 64,
    forwardTable3 (7232 + m.val) < 2^112 ∧ backwardTable3 (7232 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block114 : ∀ m : Fin 64,
    forwardTable3 (7296 + m.val) < 2^112 ∧ backwardTable3 (7296 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block115 : ∀ m : Fin 64,
    forwardTable3 (7360 + m.val) < 2^112 ∧ backwardTable3 (7360 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block116 : ∀ m : Fin 64,
    forwardTable3 (7424 + m.val) < 2^112 ∧ backwardTable3 (7424 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block117 : ∀ m : Fin 64,
    forwardTable3 (7488 + m.val) < 2^112 ∧ backwardTable3 (7488 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block118 : ∀ m : Fin 64,
    forwardTable3 (7552 + m.val) < 2^112 ∧ backwardTable3 (7552 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block119 : ∀ m : Fin 64,
    forwardTable3 (7616 + m.val) < 2^112 ∧ backwardTable3 (7616 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block120 : ∀ m : Fin 64,
    forwardTable3 (7680 + m.val) < 2^112 ∧ backwardTable3 (7680 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block121 : ∀ m : Fin 64,
    forwardTable3 (7744 + m.val) < 2^112 ∧ backwardTable3 (7744 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block122 : ∀ m : Fin 64,
    forwardTable3 (7808 + m.val) < 2^112 ∧ backwardTable3 (7808 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block123 : ∀ m : Fin 64,
    forwardTable3 (7872 + m.val) < 2^112 ∧ backwardTable3 (7872 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block124 : ∀ m : Fin 64,
    forwardTable3 (7936 + m.val) < 2^112 ∧ backwardTable3 (7936 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block125 : ∀ m : Fin 64,
    forwardTable3 (8000 + m.val) < 2^112 ∧ backwardTable3 (8000 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block126 : ∀ m : Fin 64,
    forwardTable3 (8064 + m.val) < 2^112 ∧ backwardTable3 (8064 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds3_block127 : ∀ m : Fin 64,
    forwardTable3 (8128 + m.val) < 2^112 ∧ backwardTable3 (8128 + m.val) < 2^112 := by
  decide +kernel

theorem bounds3 (m : Fin 8192) :
    forwardTable3 m.val < 2^112 ∧ backwardTable3 m.val < 2^112 := by
  apply check_blocks (P := fun a => forwardTable3 a < 2^112 ∧ backwardTable3 a < 2^112)
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact bounds3_block0
  · exact bounds3_block1
  · exact bounds3_block2
  · exact bounds3_block3
  · exact bounds3_block4
  · exact bounds3_block5
  · exact bounds3_block6
  · exact bounds3_block7
  · exact bounds3_block8
  · exact bounds3_block9
  · exact bounds3_block10
  · exact bounds3_block11
  · exact bounds3_block12
  · exact bounds3_block13
  · exact bounds3_block14
  · exact bounds3_block15
  · exact bounds3_block16
  · exact bounds3_block17
  · exact bounds3_block18
  · exact bounds3_block19
  · exact bounds3_block20
  · exact bounds3_block21
  · exact bounds3_block22
  · exact bounds3_block23
  · exact bounds3_block24
  · exact bounds3_block25
  · exact bounds3_block26
  · exact bounds3_block27
  · exact bounds3_block28
  · exact bounds3_block29
  · exact bounds3_block30
  · exact bounds3_block31
  · exact bounds3_block32
  · exact bounds3_block33
  · exact bounds3_block34
  · exact bounds3_block35
  · exact bounds3_block36
  · exact bounds3_block37
  · exact bounds3_block38
  · exact bounds3_block39
  · exact bounds3_block40
  · exact bounds3_block41
  · exact bounds3_block42
  · exact bounds3_block43
  · exact bounds3_block44
  · exact bounds3_block45
  · exact bounds3_block46
  · exact bounds3_block47
  · exact bounds3_block48
  · exact bounds3_block49
  · exact bounds3_block50
  · exact bounds3_block51
  · exact bounds3_block52
  · exact bounds3_block53
  · exact bounds3_block54
  · exact bounds3_block55
  · exact bounds3_block56
  · exact bounds3_block57
  · exact bounds3_block58
  · exact bounds3_block59
  · exact bounds3_block60
  · exact bounds3_block61
  · exact bounds3_block62
  · exact bounds3_block63
  · exact bounds3_block64
  · exact bounds3_block65
  · exact bounds3_block66
  · exact bounds3_block67
  · exact bounds3_block68
  · exact bounds3_block69
  · exact bounds3_block70
  · exact bounds3_block71
  · exact bounds3_block72
  · exact bounds3_block73
  · exact bounds3_block74
  · exact bounds3_block75
  · exact bounds3_block76
  · exact bounds3_block77
  · exact bounds3_block78
  · exact bounds3_block79
  · exact bounds3_block80
  · exact bounds3_block81
  · exact bounds3_block82
  · exact bounds3_block83
  · exact bounds3_block84
  · exact bounds3_block85
  · exact bounds3_block86
  · exact bounds3_block87
  · exact bounds3_block88
  · exact bounds3_block89
  · exact bounds3_block90
  · exact bounds3_block91
  · exact bounds3_block92
  · exact bounds3_block93
  · exact bounds3_block94
  · exact bounds3_block95
  · exact bounds3_block96
  · exact bounds3_block97
  · exact bounds3_block98
  · exact bounds3_block99
  · exact bounds3_block100
  · exact bounds3_block101
  · exact bounds3_block102
  · exact bounds3_block103
  · exact bounds3_block104
  · exact bounds3_block105
  · exact bounds3_block106
  · exact bounds3_block107
  · exact bounds3_block108
  · exact bounds3_block109
  · exact bounds3_block110
  · exact bounds3_block111
  · exact bounds3_block112
  · exact bounds3_block113
  · exact bounds3_block114
  · exact bounds3_block115
  · exact bounds3_block116
  · exact bounds3_block117
  · exact bounds3_block118
  · exact bounds3_block119
  · exact bounds3_block120
  · exact bounds3_block121
  · exact bounds3_block122
  · exact bounds3_block123
  · exact bounds3_block124
  · exact bounds3_block125
  · exact bounds3_block126
  · exact bounds3_block127

set_option maxRecDepth 10000 in
private theorem matches3_block0 : ∀ m : Fin 64,
    (forwardTable3 (0 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (0 + m.val))).val → Listed 3 (0 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block1 : ∀ m : Fin 64,
    (forwardTable3 (64 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (64 + m.val))).val → Listed 3 (64 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block2 : ∀ m : Fin 64,
    (forwardTable3 (128 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (128 + m.val))).val → Listed 3 (128 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block3 : ∀ m : Fin 64,
    (forwardTable3 (192 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (192 + m.val))).val → Listed 3 (192 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block4 : ∀ m : Fin 64,
    (forwardTable3 (256 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (256 + m.val))).val → Listed 3 (256 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block5 : ∀ m : Fin 64,
    (forwardTable3 (320 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (320 + m.val))).val → Listed 3 (320 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block6 : ∀ m : Fin 64,
    (forwardTable3 (384 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (384 + m.val))).val → Listed 3 (384 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block7 : ∀ m : Fin 64,
    (forwardTable3 (448 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (448 + m.val))).val → Listed 3 (448 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block8 : ∀ m : Fin 64,
    (forwardTable3 (512 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (512 + m.val))).val → Listed 3 (512 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block9 : ∀ m : Fin 64,
    (forwardTable3 (576 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (576 + m.val))).val → Listed 3 (576 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block10 : ∀ m : Fin 64,
    (forwardTable3 (640 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (640 + m.val))).val → Listed 3 (640 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block11 : ∀ m : Fin 64,
    (forwardTable3 (704 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (704 + m.val))).val → Listed 3 (704 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block12 : ∀ m : Fin 64,
    (forwardTable3 (768 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (768 + m.val))).val → Listed 3 (768 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block13 : ∀ m : Fin 64,
    (forwardTable3 (832 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (832 + m.val))).val → Listed 3 (832 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block14 : ∀ m : Fin 64,
    (forwardTable3 (896 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (896 + m.val))).val → Listed 3 (896 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block15 : ∀ m : Fin 64,
    (forwardTable3 (960 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (960 + m.val))).val → Listed 3 (960 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block16 : ∀ m : Fin 64,
    (forwardTable3 (1024 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1024 + m.val))).val → Listed 3 (1024 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block17 : ∀ m : Fin 64,
    (forwardTable3 (1088 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1088 + m.val))).val → Listed 3 (1088 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block18 : ∀ m : Fin 64,
    (forwardTable3 (1152 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1152 + m.val))).val → Listed 3 (1152 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block19 : ∀ m : Fin 64,
    (forwardTable3 (1216 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1216 + m.val))).val → Listed 3 (1216 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block20 : ∀ m : Fin 64,
    (forwardTable3 (1280 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1280 + m.val))).val → Listed 3 (1280 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block21 : ∀ m : Fin 64,
    (forwardTable3 (1344 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1344 + m.val))).val → Listed 3 (1344 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block22 : ∀ m : Fin 64,
    (forwardTable3 (1408 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1408 + m.val))).val → Listed 3 (1408 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block23 : ∀ m : Fin 64,
    (forwardTable3 (1472 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1472 + m.val))).val → Listed 3 (1472 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block24 : ∀ m : Fin 64,
    (forwardTable3 (1536 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1536 + m.val))).val → Listed 3 (1536 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block25 : ∀ m : Fin 64,
    (forwardTable3 (1600 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1600 + m.val))).val → Listed 3 (1600 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block26 : ∀ m : Fin 64,
    (forwardTable3 (1664 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1664 + m.val))).val → Listed 3 (1664 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block27 : ∀ m : Fin 64,
    (forwardTable3 (1728 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1728 + m.val))).val → Listed 3 (1728 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block28 : ∀ m : Fin 64,
    (forwardTable3 (1792 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1792 + m.val))).val → Listed 3 (1792 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block29 : ∀ m : Fin 64,
    (forwardTable3 (1856 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1856 + m.val))).val → Listed 3 (1856 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block30 : ∀ m : Fin 64,
    (forwardTable3 (1920 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1920 + m.val))).val → Listed 3 (1920 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block31 : ∀ m : Fin 64,
    (forwardTable3 (1984 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (1984 + m.val))).val → Listed 3 (1984 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block32 : ∀ m : Fin 64,
    (forwardTable3 (2048 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2048 + m.val))).val → Listed 3 (2048 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block33 : ∀ m : Fin 64,
    (forwardTable3 (2112 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2112 + m.val))).val → Listed 3 (2112 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block34 : ∀ m : Fin 64,
    (forwardTable3 (2176 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2176 + m.val))).val → Listed 3 (2176 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block35 : ∀ m : Fin 64,
    (forwardTable3 (2240 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2240 + m.val))).val → Listed 3 (2240 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block36 : ∀ m : Fin 64,
    (forwardTable3 (2304 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2304 + m.val))).val → Listed 3 (2304 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block37 : ∀ m : Fin 64,
    (forwardTable3 (2368 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2368 + m.val))).val → Listed 3 (2368 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block38 : ∀ m : Fin 64,
    (forwardTable3 (2432 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2432 + m.val))).val → Listed 3 (2432 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block39 : ∀ m : Fin 64,
    (forwardTable3 (2496 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2496 + m.val))).val → Listed 3 (2496 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block40 : ∀ m : Fin 64,
    (forwardTable3 (2560 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2560 + m.val))).val → Listed 3 (2560 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block41 : ∀ m : Fin 64,
    (forwardTable3 (2624 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2624 + m.val))).val → Listed 3 (2624 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block42 : ∀ m : Fin 64,
    (forwardTable3 (2688 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2688 + m.val))).val → Listed 3 (2688 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block43 : ∀ m : Fin 64,
    (forwardTable3 (2752 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2752 + m.val))).val → Listed 3 (2752 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block44 : ∀ m : Fin 64,
    (forwardTable3 (2816 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2816 + m.val))).val → Listed 3 (2816 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block45 : ∀ m : Fin 64,
    (forwardTable3 (2880 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2880 + m.val))).val → Listed 3 (2880 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block46 : ∀ m : Fin 64,
    (forwardTable3 (2944 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (2944 + m.val))).val → Listed 3 (2944 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block47 : ∀ m : Fin 64,
    (forwardTable3 (3008 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3008 + m.val))).val → Listed 3 (3008 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block48 : ∀ m : Fin 64,
    (forwardTable3 (3072 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3072 + m.val))).val → Listed 3 (3072 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block49 : ∀ m : Fin 64,
    (forwardTable3 (3136 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3136 + m.val))).val → Listed 3 (3136 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block50 : ∀ m : Fin 64,
    (forwardTable3 (3200 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3200 + m.val))).val → Listed 3 (3200 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block51 : ∀ m : Fin 64,
    (forwardTable3 (3264 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3264 + m.val))).val → Listed 3 (3264 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block52 : ∀ m : Fin 64,
    (forwardTable3 (3328 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3328 + m.val))).val → Listed 3 (3328 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block53 : ∀ m : Fin 64,
    (forwardTable3 (3392 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3392 + m.val))).val → Listed 3 (3392 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block54 : ∀ m : Fin 64,
    (forwardTable3 (3456 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3456 + m.val))).val → Listed 3 (3456 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block55 : ∀ m : Fin 64,
    (forwardTable3 (3520 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3520 + m.val))).val → Listed 3 (3520 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block56 : ∀ m : Fin 64,
    (forwardTable3 (3584 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3584 + m.val))).val → Listed 3 (3584 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block57 : ∀ m : Fin 64,
    (forwardTable3 (3648 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3648 + m.val))).val → Listed 3 (3648 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block58 : ∀ m : Fin 64,
    (forwardTable3 (3712 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3712 + m.val))).val → Listed 3 (3712 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block59 : ∀ m : Fin 64,
    (forwardTable3 (3776 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3776 + m.val))).val → Listed 3 (3776 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block60 : ∀ m : Fin 64,
    (forwardTable3 (3840 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3840 + m.val))).val → Listed 3 (3840 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block61 : ∀ m : Fin 64,
    (forwardTable3 (3904 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3904 + m.val))).val → Listed 3 (3904 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block62 : ∀ m : Fin 64,
    (forwardTable3 (3968 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (3968 + m.val))).val → Listed 3 (3968 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block63 : ∀ m : Fin 64,
    (forwardTable3 (4032 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4032 + m.val))).val → Listed 3 (4032 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block64 : ∀ m : Fin 64,
    (forwardTable3 (4096 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4096 + m.val))).val → Listed 3 (4096 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block65 : ∀ m : Fin 64,
    (forwardTable3 (4160 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4160 + m.val))).val → Listed 3 (4160 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block66 : ∀ m : Fin 64,
    (forwardTable3 (4224 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4224 + m.val))).val → Listed 3 (4224 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block67 : ∀ m : Fin 64,
    (forwardTable3 (4288 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4288 + m.val))).val → Listed 3 (4288 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block68 : ∀ m : Fin 64,
    (forwardTable3 (4352 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4352 + m.val))).val → Listed 3 (4352 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block69 : ∀ m : Fin 64,
    (forwardTable3 (4416 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4416 + m.val))).val → Listed 3 (4416 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block70 : ∀ m : Fin 64,
    (forwardTable3 (4480 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4480 + m.val))).val → Listed 3 (4480 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block71 : ∀ m : Fin 64,
    (forwardTable3 (4544 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4544 + m.val))).val → Listed 3 (4544 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block72 : ∀ m : Fin 64,
    (forwardTable3 (4608 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4608 + m.val))).val → Listed 3 (4608 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block73 : ∀ m : Fin 64,
    (forwardTable3 (4672 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4672 + m.val))).val → Listed 3 (4672 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block74 : ∀ m : Fin 64,
    (forwardTable3 (4736 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4736 + m.val))).val → Listed 3 (4736 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block75 : ∀ m : Fin 64,
    (forwardTable3 (4800 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4800 + m.val))).val → Listed 3 (4800 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block76 : ∀ m : Fin 64,
    (forwardTable3 (4864 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4864 + m.val))).val → Listed 3 (4864 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block77 : ∀ m : Fin 64,
    (forwardTable3 (4928 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4928 + m.val))).val → Listed 3 (4928 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block78 : ∀ m : Fin 64,
    (forwardTable3 (4992 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (4992 + m.val))).val → Listed 3 (4992 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block79 : ∀ m : Fin 64,
    (forwardTable3 (5056 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5056 + m.val))).val → Listed 3 (5056 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block80 : ∀ m : Fin 64,
    (forwardTable3 (5120 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5120 + m.val))).val → Listed 3 (5120 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block81 : ∀ m : Fin 64,
    (forwardTable3 (5184 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5184 + m.val))).val → Listed 3 (5184 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block82 : ∀ m : Fin 64,
    (forwardTable3 (5248 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5248 + m.val))).val → Listed 3 (5248 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block83 : ∀ m : Fin 64,
    (forwardTable3 (5312 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5312 + m.val))).val → Listed 3 (5312 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block84 : ∀ m : Fin 64,
    (forwardTable3 (5376 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5376 + m.val))).val → Listed 3 (5376 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block85 : ∀ m : Fin 64,
    (forwardTable3 (5440 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5440 + m.val))).val → Listed 3 (5440 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block86 : ∀ m : Fin 64,
    (forwardTable3 (5504 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5504 + m.val))).val → Listed 3 (5504 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block87 : ∀ m : Fin 64,
    (forwardTable3 (5568 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5568 + m.val))).val → Listed 3 (5568 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block88 : ∀ m : Fin 64,
    (forwardTable3 (5632 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5632 + m.val))).val → Listed 3 (5632 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block89 : ∀ m : Fin 64,
    (forwardTable3 (5696 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5696 + m.val))).val → Listed 3 (5696 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block90 : ∀ m : Fin 64,
    (forwardTable3 (5760 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5760 + m.val))).val → Listed 3 (5760 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block91 : ∀ m : Fin 64,
    (forwardTable3 (5824 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5824 + m.val))).val → Listed 3 (5824 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block92 : ∀ m : Fin 64,
    (forwardTable3 (5888 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5888 + m.val))).val → Listed 3 (5888 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block93 : ∀ m : Fin 64,
    (forwardTable3 (5952 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (5952 + m.val))).val → Listed 3 (5952 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block94 : ∀ m : Fin 64,
    (forwardTable3 (6016 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6016 + m.val))).val → Listed 3 (6016 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block95 : ∀ m : Fin 64,
    (forwardTable3 (6080 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6080 + m.val))).val → Listed 3 (6080 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block96 : ∀ m : Fin 64,
    (forwardTable3 (6144 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6144 + m.val))).val → Listed 3 (6144 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block97 : ∀ m : Fin 64,
    (forwardTable3 (6208 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6208 + m.val))).val → Listed 3 (6208 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block98 : ∀ m : Fin 64,
    (forwardTable3 (6272 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6272 + m.val))).val → Listed 3 (6272 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block99 : ∀ m : Fin 64,
    (forwardTable3 (6336 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6336 + m.val))).val → Listed 3 (6336 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block100 : ∀ m : Fin 64,
    (forwardTable3 (6400 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6400 + m.val))).val → Listed 3 (6400 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block101 : ∀ m : Fin 64,
    (forwardTable3 (6464 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6464 + m.val))).val → Listed 3 (6464 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block102 : ∀ m : Fin 64,
    (forwardTable3 (6528 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6528 + m.val))).val → Listed 3 (6528 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block103 : ∀ m : Fin 64,
    (forwardTable3 (6592 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6592 + m.val))).val → Listed 3 (6592 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block104 : ∀ m : Fin 64,
    (forwardTable3 (6656 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6656 + m.val))).val → Listed 3 (6656 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block105 : ∀ m : Fin 64,
    (forwardTable3 (6720 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6720 + m.val))).val → Listed 3 (6720 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block106 : ∀ m : Fin 64,
    (forwardTable3 (6784 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6784 + m.val))).val → Listed 3 (6784 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block107 : ∀ m : Fin 64,
    (forwardTable3 (6848 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6848 + m.val))).val → Listed 3 (6848 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block108 : ∀ m : Fin 64,
    (forwardTable3 (6912 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6912 + m.val))).val → Listed 3 (6912 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block109 : ∀ m : Fin 64,
    (forwardTable3 (6976 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (6976 + m.val))).val → Listed 3 (6976 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block110 : ∀ m : Fin 64,
    (forwardTable3 (7040 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7040 + m.val))).val → Listed 3 (7040 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block111 : ∀ m : Fin 64,
    (forwardTable3 (7104 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7104 + m.val))).val → Listed 3 (7104 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block112 : ∀ m : Fin 64,
    (forwardTable3 (7168 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7168 + m.val))).val → Listed 3 (7168 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block113 : ∀ m : Fin 64,
    (forwardTable3 (7232 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7232 + m.val))).val → Listed 3 (7232 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block114 : ∀ m : Fin 64,
    (forwardTable3 (7296 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7296 + m.val))).val → Listed 3 (7296 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block115 : ∀ m : Fin 64,
    (forwardTable3 (7360 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7360 + m.val))).val → Listed 3 (7360 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block116 : ∀ m : Fin 64,
    (forwardTable3 (7424 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7424 + m.val))).val → Listed 3 (7424 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block117 : ∀ m : Fin 64,
    (forwardTable3 (7488 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7488 + m.val))).val → Listed 3 (7488 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block118 : ∀ m : Fin 64,
    (forwardTable3 (7552 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7552 + m.val))).val → Listed 3 (7552 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block119 : ∀ m : Fin 64,
    (forwardTable3 (7616 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7616 + m.val))).val → Listed 3 (7616 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block120 : ∀ m : Fin 64,
    (forwardTable3 (7680 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7680 + m.val))).val → Listed 3 (7680 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block121 : ∀ m : Fin 64,
    (forwardTable3 (7744 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7744 + m.val))).val → Listed 3 (7744 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block122 : ∀ m : Fin 64,
    (forwardTable3 (7808 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7808 + m.val))).val → Listed 3 (7808 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block123 : ∀ m : Fin 64,
    (forwardTable3 (7872 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7872 + m.val))).val → Listed 3 (7872 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block124 : ∀ m : Fin 64,
    (forwardTable3 (7936 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (7936 + m.val))).val → Listed 3 (7936 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block125 : ∀ m : Fin 64,
    (forwardTable3 (8000 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (8000 + m.val))).val → Listed 3 (8000 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block126 : ∀ m : Fin 64,
    (forwardTable3 (8064 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (8064 + m.val))).val → Listed 3 (8064 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches3_block127 : ∀ m : Fin 64,
    (forwardTable3 (8128 + m.val) = backwardTable3 (reverseCode (Fin.ofNat 8192 (8128 + m.val))).val → Listed 3 (8128 + m.val)) := by
  decide +kernel

theorem matches3 (m : Fin 8192) :
    (forwardTable3 m.val = backwardTable3 (reverseCode (Fin.ofNat 8192 m.val)).val → Listed 3 m.val) := by
  apply check_blocks (P := fun a => (forwardTable3 a = backwardTable3 (reverseCode (Fin.ofNat 8192 a)).val → Listed 3 a))
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact matches3_block0
  · exact matches3_block1
  · exact matches3_block2
  · exact matches3_block3
  · exact matches3_block4
  · exact matches3_block5
  · exact matches3_block6
  · exact matches3_block7
  · exact matches3_block8
  · exact matches3_block9
  · exact matches3_block10
  · exact matches3_block11
  · exact matches3_block12
  · exact matches3_block13
  · exact matches3_block14
  · exact matches3_block15
  · exact matches3_block16
  · exact matches3_block17
  · exact matches3_block18
  · exact matches3_block19
  · exact matches3_block20
  · exact matches3_block21
  · exact matches3_block22
  · exact matches3_block23
  · exact matches3_block24
  · exact matches3_block25
  · exact matches3_block26
  · exact matches3_block27
  · exact matches3_block28
  · exact matches3_block29
  · exact matches3_block30
  · exact matches3_block31
  · exact matches3_block32
  · exact matches3_block33
  · exact matches3_block34
  · exact matches3_block35
  · exact matches3_block36
  · exact matches3_block37
  · exact matches3_block38
  · exact matches3_block39
  · exact matches3_block40
  · exact matches3_block41
  · exact matches3_block42
  · exact matches3_block43
  · exact matches3_block44
  · exact matches3_block45
  · exact matches3_block46
  · exact matches3_block47
  · exact matches3_block48
  · exact matches3_block49
  · exact matches3_block50
  · exact matches3_block51
  · exact matches3_block52
  · exact matches3_block53
  · exact matches3_block54
  · exact matches3_block55
  · exact matches3_block56
  · exact matches3_block57
  · exact matches3_block58
  · exact matches3_block59
  · exact matches3_block60
  · exact matches3_block61
  · exact matches3_block62
  · exact matches3_block63
  · exact matches3_block64
  · exact matches3_block65
  · exact matches3_block66
  · exact matches3_block67
  · exact matches3_block68
  · exact matches3_block69
  · exact matches3_block70
  · exact matches3_block71
  · exact matches3_block72
  · exact matches3_block73
  · exact matches3_block74
  · exact matches3_block75
  · exact matches3_block76
  · exact matches3_block77
  · exact matches3_block78
  · exact matches3_block79
  · exact matches3_block80
  · exact matches3_block81
  · exact matches3_block82
  · exact matches3_block83
  · exact matches3_block84
  · exact matches3_block85
  · exact matches3_block86
  · exact matches3_block87
  · exact matches3_block88
  · exact matches3_block89
  · exact matches3_block90
  · exact matches3_block91
  · exact matches3_block92
  · exact matches3_block93
  · exact matches3_block94
  · exact matches3_block95
  · exact matches3_block96
  · exact matches3_block97
  · exact matches3_block98
  · exact matches3_block99
  · exact matches3_block100
  · exact matches3_block101
  · exact matches3_block102
  · exact matches3_block103
  · exact matches3_block104
  · exact matches3_block105
  · exact matches3_block106
  · exact matches3_block107
  · exact matches3_block108
  · exact matches3_block109
  · exact matches3_block110
  · exact matches3_block111
  · exact matches3_block112
  · exact matches3_block113
  · exact matches3_block114
  · exact matches3_block115
  · exact matches3_block116
  · exact matches3_block117
  · exact matches3_block118
  · exact matches3_block119
  · exact matches3_block120
  · exact matches3_block121
  · exact matches3_block122
  · exact matches3_block123
  · exact matches3_block124
  · exact matches3_block125
  · exact matches3_block126
  · exact matches3_block127


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
