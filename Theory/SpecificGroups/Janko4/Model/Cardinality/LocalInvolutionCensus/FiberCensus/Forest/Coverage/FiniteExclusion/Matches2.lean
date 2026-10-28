module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Witnesses

/-!
# Bounds and mask witnesses for fiber 2

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
theorem backward_zero2 : backwardTable2 0 = liftEntry 2 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block0 : ∀ m : Fin 64,
    forwardTable2 (0 + m.val) < 2^112 ∧ backwardTable2 (0 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block1 : ∀ m : Fin 64,
    forwardTable2 (64 + m.val) < 2^112 ∧ backwardTable2 (64 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block2 : ∀ m : Fin 64,
    forwardTable2 (128 + m.val) < 2^112 ∧ backwardTable2 (128 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block3 : ∀ m : Fin 64,
    forwardTable2 (192 + m.val) < 2^112 ∧ backwardTable2 (192 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block4 : ∀ m : Fin 64,
    forwardTable2 (256 + m.val) < 2^112 ∧ backwardTable2 (256 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block5 : ∀ m : Fin 64,
    forwardTable2 (320 + m.val) < 2^112 ∧ backwardTable2 (320 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block6 : ∀ m : Fin 64,
    forwardTable2 (384 + m.val) < 2^112 ∧ backwardTable2 (384 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block7 : ∀ m : Fin 64,
    forwardTable2 (448 + m.val) < 2^112 ∧ backwardTable2 (448 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block8 : ∀ m : Fin 64,
    forwardTable2 (512 + m.val) < 2^112 ∧ backwardTable2 (512 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block9 : ∀ m : Fin 64,
    forwardTable2 (576 + m.val) < 2^112 ∧ backwardTable2 (576 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block10 : ∀ m : Fin 64,
    forwardTable2 (640 + m.val) < 2^112 ∧ backwardTable2 (640 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block11 : ∀ m : Fin 64,
    forwardTable2 (704 + m.val) < 2^112 ∧ backwardTable2 (704 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block12 : ∀ m : Fin 64,
    forwardTable2 (768 + m.val) < 2^112 ∧ backwardTable2 (768 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block13 : ∀ m : Fin 64,
    forwardTable2 (832 + m.val) < 2^112 ∧ backwardTable2 (832 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block14 : ∀ m : Fin 64,
    forwardTable2 (896 + m.val) < 2^112 ∧ backwardTable2 (896 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block15 : ∀ m : Fin 64,
    forwardTable2 (960 + m.val) < 2^112 ∧ backwardTable2 (960 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block16 : ∀ m : Fin 64,
    forwardTable2 (1024 + m.val) < 2^112 ∧ backwardTable2 (1024 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block17 : ∀ m : Fin 64,
    forwardTable2 (1088 + m.val) < 2^112 ∧ backwardTable2 (1088 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block18 : ∀ m : Fin 64,
    forwardTable2 (1152 + m.val) < 2^112 ∧ backwardTable2 (1152 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block19 : ∀ m : Fin 64,
    forwardTable2 (1216 + m.val) < 2^112 ∧ backwardTable2 (1216 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block20 : ∀ m : Fin 64,
    forwardTable2 (1280 + m.val) < 2^112 ∧ backwardTable2 (1280 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block21 : ∀ m : Fin 64,
    forwardTable2 (1344 + m.val) < 2^112 ∧ backwardTable2 (1344 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block22 : ∀ m : Fin 64,
    forwardTable2 (1408 + m.val) < 2^112 ∧ backwardTable2 (1408 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block23 : ∀ m : Fin 64,
    forwardTable2 (1472 + m.val) < 2^112 ∧ backwardTable2 (1472 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block24 : ∀ m : Fin 64,
    forwardTable2 (1536 + m.val) < 2^112 ∧ backwardTable2 (1536 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block25 : ∀ m : Fin 64,
    forwardTable2 (1600 + m.val) < 2^112 ∧ backwardTable2 (1600 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block26 : ∀ m : Fin 64,
    forwardTable2 (1664 + m.val) < 2^112 ∧ backwardTable2 (1664 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block27 : ∀ m : Fin 64,
    forwardTable2 (1728 + m.val) < 2^112 ∧ backwardTable2 (1728 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block28 : ∀ m : Fin 64,
    forwardTable2 (1792 + m.val) < 2^112 ∧ backwardTable2 (1792 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block29 : ∀ m : Fin 64,
    forwardTable2 (1856 + m.val) < 2^112 ∧ backwardTable2 (1856 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block30 : ∀ m : Fin 64,
    forwardTable2 (1920 + m.val) < 2^112 ∧ backwardTable2 (1920 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block31 : ∀ m : Fin 64,
    forwardTable2 (1984 + m.val) < 2^112 ∧ backwardTable2 (1984 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block32 : ∀ m : Fin 64,
    forwardTable2 (2048 + m.val) < 2^112 ∧ backwardTable2 (2048 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block33 : ∀ m : Fin 64,
    forwardTable2 (2112 + m.val) < 2^112 ∧ backwardTable2 (2112 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block34 : ∀ m : Fin 64,
    forwardTable2 (2176 + m.val) < 2^112 ∧ backwardTable2 (2176 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block35 : ∀ m : Fin 64,
    forwardTable2 (2240 + m.val) < 2^112 ∧ backwardTable2 (2240 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block36 : ∀ m : Fin 64,
    forwardTable2 (2304 + m.val) < 2^112 ∧ backwardTable2 (2304 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block37 : ∀ m : Fin 64,
    forwardTable2 (2368 + m.val) < 2^112 ∧ backwardTable2 (2368 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block38 : ∀ m : Fin 64,
    forwardTable2 (2432 + m.val) < 2^112 ∧ backwardTable2 (2432 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block39 : ∀ m : Fin 64,
    forwardTable2 (2496 + m.val) < 2^112 ∧ backwardTable2 (2496 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block40 : ∀ m : Fin 64,
    forwardTable2 (2560 + m.val) < 2^112 ∧ backwardTable2 (2560 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block41 : ∀ m : Fin 64,
    forwardTable2 (2624 + m.val) < 2^112 ∧ backwardTable2 (2624 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block42 : ∀ m : Fin 64,
    forwardTable2 (2688 + m.val) < 2^112 ∧ backwardTable2 (2688 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block43 : ∀ m : Fin 64,
    forwardTable2 (2752 + m.val) < 2^112 ∧ backwardTable2 (2752 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block44 : ∀ m : Fin 64,
    forwardTable2 (2816 + m.val) < 2^112 ∧ backwardTable2 (2816 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block45 : ∀ m : Fin 64,
    forwardTable2 (2880 + m.val) < 2^112 ∧ backwardTable2 (2880 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block46 : ∀ m : Fin 64,
    forwardTable2 (2944 + m.val) < 2^112 ∧ backwardTable2 (2944 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block47 : ∀ m : Fin 64,
    forwardTable2 (3008 + m.val) < 2^112 ∧ backwardTable2 (3008 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block48 : ∀ m : Fin 64,
    forwardTable2 (3072 + m.val) < 2^112 ∧ backwardTable2 (3072 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block49 : ∀ m : Fin 64,
    forwardTable2 (3136 + m.val) < 2^112 ∧ backwardTable2 (3136 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block50 : ∀ m : Fin 64,
    forwardTable2 (3200 + m.val) < 2^112 ∧ backwardTable2 (3200 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block51 : ∀ m : Fin 64,
    forwardTable2 (3264 + m.val) < 2^112 ∧ backwardTable2 (3264 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block52 : ∀ m : Fin 64,
    forwardTable2 (3328 + m.val) < 2^112 ∧ backwardTable2 (3328 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block53 : ∀ m : Fin 64,
    forwardTable2 (3392 + m.val) < 2^112 ∧ backwardTable2 (3392 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block54 : ∀ m : Fin 64,
    forwardTable2 (3456 + m.val) < 2^112 ∧ backwardTable2 (3456 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block55 : ∀ m : Fin 64,
    forwardTable2 (3520 + m.val) < 2^112 ∧ backwardTable2 (3520 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block56 : ∀ m : Fin 64,
    forwardTable2 (3584 + m.val) < 2^112 ∧ backwardTable2 (3584 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block57 : ∀ m : Fin 64,
    forwardTable2 (3648 + m.val) < 2^112 ∧ backwardTable2 (3648 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block58 : ∀ m : Fin 64,
    forwardTable2 (3712 + m.val) < 2^112 ∧ backwardTable2 (3712 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block59 : ∀ m : Fin 64,
    forwardTable2 (3776 + m.val) < 2^112 ∧ backwardTable2 (3776 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block60 : ∀ m : Fin 64,
    forwardTable2 (3840 + m.val) < 2^112 ∧ backwardTable2 (3840 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block61 : ∀ m : Fin 64,
    forwardTable2 (3904 + m.val) < 2^112 ∧ backwardTable2 (3904 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block62 : ∀ m : Fin 64,
    forwardTable2 (3968 + m.val) < 2^112 ∧ backwardTable2 (3968 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block63 : ∀ m : Fin 64,
    forwardTable2 (4032 + m.val) < 2^112 ∧ backwardTable2 (4032 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block64 : ∀ m : Fin 64,
    forwardTable2 (4096 + m.val) < 2^112 ∧ backwardTable2 (4096 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block65 : ∀ m : Fin 64,
    forwardTable2 (4160 + m.val) < 2^112 ∧ backwardTable2 (4160 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block66 : ∀ m : Fin 64,
    forwardTable2 (4224 + m.val) < 2^112 ∧ backwardTable2 (4224 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block67 : ∀ m : Fin 64,
    forwardTable2 (4288 + m.val) < 2^112 ∧ backwardTable2 (4288 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block68 : ∀ m : Fin 64,
    forwardTable2 (4352 + m.val) < 2^112 ∧ backwardTable2 (4352 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block69 : ∀ m : Fin 64,
    forwardTable2 (4416 + m.val) < 2^112 ∧ backwardTable2 (4416 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block70 : ∀ m : Fin 64,
    forwardTable2 (4480 + m.val) < 2^112 ∧ backwardTable2 (4480 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block71 : ∀ m : Fin 64,
    forwardTable2 (4544 + m.val) < 2^112 ∧ backwardTable2 (4544 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block72 : ∀ m : Fin 64,
    forwardTable2 (4608 + m.val) < 2^112 ∧ backwardTable2 (4608 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block73 : ∀ m : Fin 64,
    forwardTable2 (4672 + m.val) < 2^112 ∧ backwardTable2 (4672 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block74 : ∀ m : Fin 64,
    forwardTable2 (4736 + m.val) < 2^112 ∧ backwardTable2 (4736 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block75 : ∀ m : Fin 64,
    forwardTable2 (4800 + m.val) < 2^112 ∧ backwardTable2 (4800 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block76 : ∀ m : Fin 64,
    forwardTable2 (4864 + m.val) < 2^112 ∧ backwardTable2 (4864 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block77 : ∀ m : Fin 64,
    forwardTable2 (4928 + m.val) < 2^112 ∧ backwardTable2 (4928 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block78 : ∀ m : Fin 64,
    forwardTable2 (4992 + m.val) < 2^112 ∧ backwardTable2 (4992 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block79 : ∀ m : Fin 64,
    forwardTable2 (5056 + m.val) < 2^112 ∧ backwardTable2 (5056 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block80 : ∀ m : Fin 64,
    forwardTable2 (5120 + m.val) < 2^112 ∧ backwardTable2 (5120 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block81 : ∀ m : Fin 64,
    forwardTable2 (5184 + m.val) < 2^112 ∧ backwardTable2 (5184 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block82 : ∀ m : Fin 64,
    forwardTable2 (5248 + m.val) < 2^112 ∧ backwardTable2 (5248 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block83 : ∀ m : Fin 64,
    forwardTable2 (5312 + m.val) < 2^112 ∧ backwardTable2 (5312 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block84 : ∀ m : Fin 64,
    forwardTable2 (5376 + m.val) < 2^112 ∧ backwardTable2 (5376 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block85 : ∀ m : Fin 64,
    forwardTable2 (5440 + m.val) < 2^112 ∧ backwardTable2 (5440 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block86 : ∀ m : Fin 64,
    forwardTable2 (5504 + m.val) < 2^112 ∧ backwardTable2 (5504 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block87 : ∀ m : Fin 64,
    forwardTable2 (5568 + m.val) < 2^112 ∧ backwardTable2 (5568 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block88 : ∀ m : Fin 64,
    forwardTable2 (5632 + m.val) < 2^112 ∧ backwardTable2 (5632 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block89 : ∀ m : Fin 64,
    forwardTable2 (5696 + m.val) < 2^112 ∧ backwardTable2 (5696 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block90 : ∀ m : Fin 64,
    forwardTable2 (5760 + m.val) < 2^112 ∧ backwardTable2 (5760 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block91 : ∀ m : Fin 64,
    forwardTable2 (5824 + m.val) < 2^112 ∧ backwardTable2 (5824 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block92 : ∀ m : Fin 64,
    forwardTable2 (5888 + m.val) < 2^112 ∧ backwardTable2 (5888 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block93 : ∀ m : Fin 64,
    forwardTable2 (5952 + m.val) < 2^112 ∧ backwardTable2 (5952 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block94 : ∀ m : Fin 64,
    forwardTable2 (6016 + m.val) < 2^112 ∧ backwardTable2 (6016 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block95 : ∀ m : Fin 64,
    forwardTable2 (6080 + m.val) < 2^112 ∧ backwardTable2 (6080 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block96 : ∀ m : Fin 64,
    forwardTable2 (6144 + m.val) < 2^112 ∧ backwardTable2 (6144 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block97 : ∀ m : Fin 64,
    forwardTable2 (6208 + m.val) < 2^112 ∧ backwardTable2 (6208 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block98 : ∀ m : Fin 64,
    forwardTable2 (6272 + m.val) < 2^112 ∧ backwardTable2 (6272 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block99 : ∀ m : Fin 64,
    forwardTable2 (6336 + m.val) < 2^112 ∧ backwardTable2 (6336 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block100 : ∀ m : Fin 64,
    forwardTable2 (6400 + m.val) < 2^112 ∧ backwardTable2 (6400 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block101 : ∀ m : Fin 64,
    forwardTable2 (6464 + m.val) < 2^112 ∧ backwardTable2 (6464 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block102 : ∀ m : Fin 64,
    forwardTable2 (6528 + m.val) < 2^112 ∧ backwardTable2 (6528 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block103 : ∀ m : Fin 64,
    forwardTable2 (6592 + m.val) < 2^112 ∧ backwardTable2 (6592 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block104 : ∀ m : Fin 64,
    forwardTable2 (6656 + m.val) < 2^112 ∧ backwardTable2 (6656 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block105 : ∀ m : Fin 64,
    forwardTable2 (6720 + m.val) < 2^112 ∧ backwardTable2 (6720 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block106 : ∀ m : Fin 64,
    forwardTable2 (6784 + m.val) < 2^112 ∧ backwardTable2 (6784 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block107 : ∀ m : Fin 64,
    forwardTable2 (6848 + m.val) < 2^112 ∧ backwardTable2 (6848 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block108 : ∀ m : Fin 64,
    forwardTable2 (6912 + m.val) < 2^112 ∧ backwardTable2 (6912 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block109 : ∀ m : Fin 64,
    forwardTable2 (6976 + m.val) < 2^112 ∧ backwardTable2 (6976 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block110 : ∀ m : Fin 64,
    forwardTable2 (7040 + m.val) < 2^112 ∧ backwardTable2 (7040 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block111 : ∀ m : Fin 64,
    forwardTable2 (7104 + m.val) < 2^112 ∧ backwardTable2 (7104 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block112 : ∀ m : Fin 64,
    forwardTable2 (7168 + m.val) < 2^112 ∧ backwardTable2 (7168 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block113 : ∀ m : Fin 64,
    forwardTable2 (7232 + m.val) < 2^112 ∧ backwardTable2 (7232 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block114 : ∀ m : Fin 64,
    forwardTable2 (7296 + m.val) < 2^112 ∧ backwardTable2 (7296 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block115 : ∀ m : Fin 64,
    forwardTable2 (7360 + m.val) < 2^112 ∧ backwardTable2 (7360 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block116 : ∀ m : Fin 64,
    forwardTable2 (7424 + m.val) < 2^112 ∧ backwardTable2 (7424 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block117 : ∀ m : Fin 64,
    forwardTable2 (7488 + m.val) < 2^112 ∧ backwardTable2 (7488 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block118 : ∀ m : Fin 64,
    forwardTable2 (7552 + m.val) < 2^112 ∧ backwardTable2 (7552 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block119 : ∀ m : Fin 64,
    forwardTable2 (7616 + m.val) < 2^112 ∧ backwardTable2 (7616 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block120 : ∀ m : Fin 64,
    forwardTable2 (7680 + m.val) < 2^112 ∧ backwardTable2 (7680 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block121 : ∀ m : Fin 64,
    forwardTable2 (7744 + m.val) < 2^112 ∧ backwardTable2 (7744 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block122 : ∀ m : Fin 64,
    forwardTable2 (7808 + m.val) < 2^112 ∧ backwardTable2 (7808 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block123 : ∀ m : Fin 64,
    forwardTable2 (7872 + m.val) < 2^112 ∧ backwardTable2 (7872 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block124 : ∀ m : Fin 64,
    forwardTable2 (7936 + m.val) < 2^112 ∧ backwardTable2 (7936 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block125 : ∀ m : Fin 64,
    forwardTable2 (8000 + m.val) < 2^112 ∧ backwardTable2 (8000 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block126 : ∀ m : Fin 64,
    forwardTable2 (8064 + m.val) < 2^112 ∧ backwardTable2 (8064 + m.val) < 2^112 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bounds2_block127 : ∀ m : Fin 64,
    forwardTable2 (8128 + m.val) < 2^112 ∧ backwardTable2 (8128 + m.val) < 2^112 := by
  decide +kernel

theorem bounds2 (m : Fin 8192) :
    forwardTable2 m.val < 2^112 ∧ backwardTable2 m.val < 2^112 := by
  apply check_blocks (P := fun a => forwardTable2 a < 2^112 ∧ backwardTable2 a < 2^112)
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact bounds2_block0
  · exact bounds2_block1
  · exact bounds2_block2
  · exact bounds2_block3
  · exact bounds2_block4
  · exact bounds2_block5
  · exact bounds2_block6
  · exact bounds2_block7
  · exact bounds2_block8
  · exact bounds2_block9
  · exact bounds2_block10
  · exact bounds2_block11
  · exact bounds2_block12
  · exact bounds2_block13
  · exact bounds2_block14
  · exact bounds2_block15
  · exact bounds2_block16
  · exact bounds2_block17
  · exact bounds2_block18
  · exact bounds2_block19
  · exact bounds2_block20
  · exact bounds2_block21
  · exact bounds2_block22
  · exact bounds2_block23
  · exact bounds2_block24
  · exact bounds2_block25
  · exact bounds2_block26
  · exact bounds2_block27
  · exact bounds2_block28
  · exact bounds2_block29
  · exact bounds2_block30
  · exact bounds2_block31
  · exact bounds2_block32
  · exact bounds2_block33
  · exact bounds2_block34
  · exact bounds2_block35
  · exact bounds2_block36
  · exact bounds2_block37
  · exact bounds2_block38
  · exact bounds2_block39
  · exact bounds2_block40
  · exact bounds2_block41
  · exact bounds2_block42
  · exact bounds2_block43
  · exact bounds2_block44
  · exact bounds2_block45
  · exact bounds2_block46
  · exact bounds2_block47
  · exact bounds2_block48
  · exact bounds2_block49
  · exact bounds2_block50
  · exact bounds2_block51
  · exact bounds2_block52
  · exact bounds2_block53
  · exact bounds2_block54
  · exact bounds2_block55
  · exact bounds2_block56
  · exact bounds2_block57
  · exact bounds2_block58
  · exact bounds2_block59
  · exact bounds2_block60
  · exact bounds2_block61
  · exact bounds2_block62
  · exact bounds2_block63
  · exact bounds2_block64
  · exact bounds2_block65
  · exact bounds2_block66
  · exact bounds2_block67
  · exact bounds2_block68
  · exact bounds2_block69
  · exact bounds2_block70
  · exact bounds2_block71
  · exact bounds2_block72
  · exact bounds2_block73
  · exact bounds2_block74
  · exact bounds2_block75
  · exact bounds2_block76
  · exact bounds2_block77
  · exact bounds2_block78
  · exact bounds2_block79
  · exact bounds2_block80
  · exact bounds2_block81
  · exact bounds2_block82
  · exact bounds2_block83
  · exact bounds2_block84
  · exact bounds2_block85
  · exact bounds2_block86
  · exact bounds2_block87
  · exact bounds2_block88
  · exact bounds2_block89
  · exact bounds2_block90
  · exact bounds2_block91
  · exact bounds2_block92
  · exact bounds2_block93
  · exact bounds2_block94
  · exact bounds2_block95
  · exact bounds2_block96
  · exact bounds2_block97
  · exact bounds2_block98
  · exact bounds2_block99
  · exact bounds2_block100
  · exact bounds2_block101
  · exact bounds2_block102
  · exact bounds2_block103
  · exact bounds2_block104
  · exact bounds2_block105
  · exact bounds2_block106
  · exact bounds2_block107
  · exact bounds2_block108
  · exact bounds2_block109
  · exact bounds2_block110
  · exact bounds2_block111
  · exact bounds2_block112
  · exact bounds2_block113
  · exact bounds2_block114
  · exact bounds2_block115
  · exact bounds2_block116
  · exact bounds2_block117
  · exact bounds2_block118
  · exact bounds2_block119
  · exact bounds2_block120
  · exact bounds2_block121
  · exact bounds2_block122
  · exact bounds2_block123
  · exact bounds2_block124
  · exact bounds2_block125
  · exact bounds2_block126
  · exact bounds2_block127

set_option maxRecDepth 10000 in
private theorem matches2_block0 : ∀ m : Fin 64,
    (forwardTable2 (0 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (0 + m.val))).val → Listed 2 (0 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block1 : ∀ m : Fin 64,
    (forwardTable2 (64 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (64 + m.val))).val → Listed 2 (64 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block2 : ∀ m : Fin 64,
    (forwardTable2 (128 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (128 + m.val))).val → Listed 2 (128 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block3 : ∀ m : Fin 64,
    (forwardTable2 (192 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (192 + m.val))).val → Listed 2 (192 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block4 : ∀ m : Fin 64,
    (forwardTable2 (256 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (256 + m.val))).val → Listed 2 (256 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block5 : ∀ m : Fin 64,
    (forwardTable2 (320 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (320 + m.val))).val → Listed 2 (320 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block6 : ∀ m : Fin 64,
    (forwardTable2 (384 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (384 + m.val))).val → Listed 2 (384 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block7 : ∀ m : Fin 64,
    (forwardTable2 (448 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (448 + m.val))).val → Listed 2 (448 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block8 : ∀ m : Fin 64,
    (forwardTable2 (512 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (512 + m.val))).val → Listed 2 (512 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block9 : ∀ m : Fin 64,
    (forwardTable2 (576 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (576 + m.val))).val → Listed 2 (576 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block10 : ∀ m : Fin 64,
    (forwardTable2 (640 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (640 + m.val))).val → Listed 2 (640 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block11 : ∀ m : Fin 64,
    (forwardTable2 (704 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (704 + m.val))).val → Listed 2 (704 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block12 : ∀ m : Fin 64,
    (forwardTable2 (768 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (768 + m.val))).val → Listed 2 (768 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block13 : ∀ m : Fin 64,
    (forwardTable2 (832 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (832 + m.val))).val → Listed 2 (832 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block14 : ∀ m : Fin 64,
    (forwardTable2 (896 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (896 + m.val))).val → Listed 2 (896 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block15 : ∀ m : Fin 64,
    (forwardTable2 (960 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (960 + m.val))).val → Listed 2 (960 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block16 : ∀ m : Fin 64,
    (forwardTable2 (1024 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1024 + m.val))).val → Listed 2 (1024 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block17 : ∀ m : Fin 64,
    (forwardTable2 (1088 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1088 + m.val))).val → Listed 2 (1088 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block18 : ∀ m : Fin 64,
    (forwardTable2 (1152 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1152 + m.val))).val → Listed 2 (1152 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block19 : ∀ m : Fin 64,
    (forwardTable2 (1216 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1216 + m.val))).val → Listed 2 (1216 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block20 : ∀ m : Fin 64,
    (forwardTable2 (1280 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1280 + m.val))).val → Listed 2 (1280 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block21 : ∀ m : Fin 64,
    (forwardTable2 (1344 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1344 + m.val))).val → Listed 2 (1344 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block22 : ∀ m : Fin 64,
    (forwardTable2 (1408 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1408 + m.val))).val → Listed 2 (1408 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block23 : ∀ m : Fin 64,
    (forwardTable2 (1472 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1472 + m.val))).val → Listed 2 (1472 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block24 : ∀ m : Fin 64,
    (forwardTable2 (1536 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1536 + m.val))).val → Listed 2 (1536 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block25 : ∀ m : Fin 64,
    (forwardTable2 (1600 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1600 + m.val))).val → Listed 2 (1600 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block26 : ∀ m : Fin 64,
    (forwardTable2 (1664 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1664 + m.val))).val → Listed 2 (1664 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block27 : ∀ m : Fin 64,
    (forwardTable2 (1728 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1728 + m.val))).val → Listed 2 (1728 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block28 : ∀ m : Fin 64,
    (forwardTable2 (1792 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1792 + m.val))).val → Listed 2 (1792 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block29 : ∀ m : Fin 64,
    (forwardTable2 (1856 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1856 + m.val))).val → Listed 2 (1856 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block30 : ∀ m : Fin 64,
    (forwardTable2 (1920 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1920 + m.val))).val → Listed 2 (1920 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block31 : ∀ m : Fin 64,
    (forwardTable2 (1984 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (1984 + m.val))).val → Listed 2 (1984 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block32 : ∀ m : Fin 64,
    (forwardTable2 (2048 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2048 + m.val))).val → Listed 2 (2048 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block33 : ∀ m : Fin 64,
    (forwardTable2 (2112 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2112 + m.val))).val → Listed 2 (2112 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block34 : ∀ m : Fin 64,
    (forwardTable2 (2176 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2176 + m.val))).val → Listed 2 (2176 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block35 : ∀ m : Fin 64,
    (forwardTable2 (2240 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2240 + m.val))).val → Listed 2 (2240 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block36 : ∀ m : Fin 64,
    (forwardTable2 (2304 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2304 + m.val))).val → Listed 2 (2304 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block37 : ∀ m : Fin 64,
    (forwardTable2 (2368 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2368 + m.val))).val → Listed 2 (2368 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block38 : ∀ m : Fin 64,
    (forwardTable2 (2432 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2432 + m.val))).val → Listed 2 (2432 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block39 : ∀ m : Fin 64,
    (forwardTable2 (2496 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2496 + m.val))).val → Listed 2 (2496 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block40 : ∀ m : Fin 64,
    (forwardTable2 (2560 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2560 + m.val))).val → Listed 2 (2560 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block41 : ∀ m : Fin 64,
    (forwardTable2 (2624 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2624 + m.val))).val → Listed 2 (2624 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block42 : ∀ m : Fin 64,
    (forwardTable2 (2688 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2688 + m.val))).val → Listed 2 (2688 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block43 : ∀ m : Fin 64,
    (forwardTable2 (2752 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2752 + m.val))).val → Listed 2 (2752 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block44 : ∀ m : Fin 64,
    (forwardTable2 (2816 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2816 + m.val))).val → Listed 2 (2816 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block45 : ∀ m : Fin 64,
    (forwardTable2 (2880 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2880 + m.val))).val → Listed 2 (2880 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block46 : ∀ m : Fin 64,
    (forwardTable2 (2944 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (2944 + m.val))).val → Listed 2 (2944 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block47 : ∀ m : Fin 64,
    (forwardTable2 (3008 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3008 + m.val))).val → Listed 2 (3008 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block48 : ∀ m : Fin 64,
    (forwardTable2 (3072 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3072 + m.val))).val → Listed 2 (3072 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block49 : ∀ m : Fin 64,
    (forwardTable2 (3136 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3136 + m.val))).val → Listed 2 (3136 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block50 : ∀ m : Fin 64,
    (forwardTable2 (3200 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3200 + m.val))).val → Listed 2 (3200 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block51 : ∀ m : Fin 64,
    (forwardTable2 (3264 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3264 + m.val))).val → Listed 2 (3264 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block52 : ∀ m : Fin 64,
    (forwardTable2 (3328 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3328 + m.val))).val → Listed 2 (3328 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block53 : ∀ m : Fin 64,
    (forwardTable2 (3392 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3392 + m.val))).val → Listed 2 (3392 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block54 : ∀ m : Fin 64,
    (forwardTable2 (3456 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3456 + m.val))).val → Listed 2 (3456 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block55 : ∀ m : Fin 64,
    (forwardTable2 (3520 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3520 + m.val))).val → Listed 2 (3520 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block56 : ∀ m : Fin 64,
    (forwardTable2 (3584 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3584 + m.val))).val → Listed 2 (3584 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block57 : ∀ m : Fin 64,
    (forwardTable2 (3648 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3648 + m.val))).val → Listed 2 (3648 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block58 : ∀ m : Fin 64,
    (forwardTable2 (3712 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3712 + m.val))).val → Listed 2 (3712 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block59 : ∀ m : Fin 64,
    (forwardTable2 (3776 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3776 + m.val))).val → Listed 2 (3776 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block60 : ∀ m : Fin 64,
    (forwardTable2 (3840 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3840 + m.val))).val → Listed 2 (3840 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block61 : ∀ m : Fin 64,
    (forwardTable2 (3904 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3904 + m.val))).val → Listed 2 (3904 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block62 : ∀ m : Fin 64,
    (forwardTable2 (3968 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (3968 + m.val))).val → Listed 2 (3968 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block63 : ∀ m : Fin 64,
    (forwardTable2 (4032 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4032 + m.val))).val → Listed 2 (4032 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block64 : ∀ m : Fin 64,
    (forwardTable2 (4096 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4096 + m.val))).val → Listed 2 (4096 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block65 : ∀ m : Fin 64,
    (forwardTable2 (4160 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4160 + m.val))).val → Listed 2 (4160 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block66 : ∀ m : Fin 64,
    (forwardTable2 (4224 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4224 + m.val))).val → Listed 2 (4224 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block67 : ∀ m : Fin 64,
    (forwardTable2 (4288 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4288 + m.val))).val → Listed 2 (4288 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block68 : ∀ m : Fin 64,
    (forwardTable2 (4352 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4352 + m.val))).val → Listed 2 (4352 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block69 : ∀ m : Fin 64,
    (forwardTable2 (4416 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4416 + m.val))).val → Listed 2 (4416 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block70 : ∀ m : Fin 64,
    (forwardTable2 (4480 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4480 + m.val))).val → Listed 2 (4480 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block71 : ∀ m : Fin 64,
    (forwardTable2 (4544 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4544 + m.val))).val → Listed 2 (4544 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block72 : ∀ m : Fin 64,
    (forwardTable2 (4608 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4608 + m.val))).val → Listed 2 (4608 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block73 : ∀ m : Fin 64,
    (forwardTable2 (4672 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4672 + m.val))).val → Listed 2 (4672 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block74 : ∀ m : Fin 64,
    (forwardTable2 (4736 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4736 + m.val))).val → Listed 2 (4736 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block75 : ∀ m : Fin 64,
    (forwardTable2 (4800 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4800 + m.val))).val → Listed 2 (4800 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block76 : ∀ m : Fin 64,
    (forwardTable2 (4864 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4864 + m.val))).val → Listed 2 (4864 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block77 : ∀ m : Fin 64,
    (forwardTable2 (4928 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4928 + m.val))).val → Listed 2 (4928 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block78 : ∀ m : Fin 64,
    (forwardTable2 (4992 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (4992 + m.val))).val → Listed 2 (4992 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block79 : ∀ m : Fin 64,
    (forwardTable2 (5056 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5056 + m.val))).val → Listed 2 (5056 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block80 : ∀ m : Fin 64,
    (forwardTable2 (5120 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5120 + m.val))).val → Listed 2 (5120 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block81 : ∀ m : Fin 64,
    (forwardTable2 (5184 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5184 + m.val))).val → Listed 2 (5184 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block82 : ∀ m : Fin 64,
    (forwardTable2 (5248 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5248 + m.val))).val → Listed 2 (5248 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block83 : ∀ m : Fin 64,
    (forwardTable2 (5312 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5312 + m.val))).val → Listed 2 (5312 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block84 : ∀ m : Fin 64,
    (forwardTable2 (5376 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5376 + m.val))).val → Listed 2 (5376 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block85 : ∀ m : Fin 64,
    (forwardTable2 (5440 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5440 + m.val))).val → Listed 2 (5440 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block86 : ∀ m : Fin 64,
    (forwardTable2 (5504 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5504 + m.val))).val → Listed 2 (5504 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block87 : ∀ m : Fin 64,
    (forwardTable2 (5568 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5568 + m.val))).val → Listed 2 (5568 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block88 : ∀ m : Fin 64,
    (forwardTable2 (5632 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5632 + m.val))).val → Listed 2 (5632 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block89 : ∀ m : Fin 64,
    (forwardTable2 (5696 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5696 + m.val))).val → Listed 2 (5696 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block90 : ∀ m : Fin 64,
    (forwardTable2 (5760 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5760 + m.val))).val → Listed 2 (5760 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block91 : ∀ m : Fin 64,
    (forwardTable2 (5824 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5824 + m.val))).val → Listed 2 (5824 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block92 : ∀ m : Fin 64,
    (forwardTable2 (5888 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5888 + m.val))).val → Listed 2 (5888 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block93 : ∀ m : Fin 64,
    (forwardTable2 (5952 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (5952 + m.val))).val → Listed 2 (5952 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block94 : ∀ m : Fin 64,
    (forwardTable2 (6016 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6016 + m.val))).val → Listed 2 (6016 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block95 : ∀ m : Fin 64,
    (forwardTable2 (6080 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6080 + m.val))).val → Listed 2 (6080 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block96 : ∀ m : Fin 64,
    (forwardTable2 (6144 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6144 + m.val))).val → Listed 2 (6144 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block97 : ∀ m : Fin 64,
    (forwardTable2 (6208 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6208 + m.val))).val → Listed 2 (6208 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block98 : ∀ m : Fin 64,
    (forwardTable2 (6272 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6272 + m.val))).val → Listed 2 (6272 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block99 : ∀ m : Fin 64,
    (forwardTable2 (6336 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6336 + m.val))).val → Listed 2 (6336 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block100 : ∀ m : Fin 64,
    (forwardTable2 (6400 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6400 + m.val))).val → Listed 2 (6400 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block101 : ∀ m : Fin 64,
    (forwardTable2 (6464 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6464 + m.val))).val → Listed 2 (6464 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block102 : ∀ m : Fin 64,
    (forwardTable2 (6528 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6528 + m.val))).val → Listed 2 (6528 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block103 : ∀ m : Fin 64,
    (forwardTable2 (6592 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6592 + m.val))).val → Listed 2 (6592 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block104 : ∀ m : Fin 64,
    (forwardTable2 (6656 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6656 + m.val))).val → Listed 2 (6656 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block105 : ∀ m : Fin 64,
    (forwardTable2 (6720 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6720 + m.val))).val → Listed 2 (6720 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block106 : ∀ m : Fin 64,
    (forwardTable2 (6784 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6784 + m.val))).val → Listed 2 (6784 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block107 : ∀ m : Fin 64,
    (forwardTable2 (6848 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6848 + m.val))).val → Listed 2 (6848 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block108 : ∀ m : Fin 64,
    (forwardTable2 (6912 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6912 + m.val))).val → Listed 2 (6912 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block109 : ∀ m : Fin 64,
    (forwardTable2 (6976 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (6976 + m.val))).val → Listed 2 (6976 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block110 : ∀ m : Fin 64,
    (forwardTable2 (7040 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7040 + m.val))).val → Listed 2 (7040 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block111 : ∀ m : Fin 64,
    (forwardTable2 (7104 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7104 + m.val))).val → Listed 2 (7104 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block112 : ∀ m : Fin 64,
    (forwardTable2 (7168 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7168 + m.val))).val → Listed 2 (7168 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block113 : ∀ m : Fin 64,
    (forwardTable2 (7232 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7232 + m.val))).val → Listed 2 (7232 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block114 : ∀ m : Fin 64,
    (forwardTable2 (7296 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7296 + m.val))).val → Listed 2 (7296 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block115 : ∀ m : Fin 64,
    (forwardTable2 (7360 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7360 + m.val))).val → Listed 2 (7360 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block116 : ∀ m : Fin 64,
    (forwardTable2 (7424 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7424 + m.val))).val → Listed 2 (7424 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block117 : ∀ m : Fin 64,
    (forwardTable2 (7488 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7488 + m.val))).val → Listed 2 (7488 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block118 : ∀ m : Fin 64,
    (forwardTable2 (7552 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7552 + m.val))).val → Listed 2 (7552 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block119 : ∀ m : Fin 64,
    (forwardTable2 (7616 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7616 + m.val))).val → Listed 2 (7616 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block120 : ∀ m : Fin 64,
    (forwardTable2 (7680 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7680 + m.val))).val → Listed 2 (7680 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block121 : ∀ m : Fin 64,
    (forwardTable2 (7744 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7744 + m.val))).val → Listed 2 (7744 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block122 : ∀ m : Fin 64,
    (forwardTable2 (7808 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7808 + m.val))).val → Listed 2 (7808 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block123 : ∀ m : Fin 64,
    (forwardTable2 (7872 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7872 + m.val))).val → Listed 2 (7872 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block124 : ∀ m : Fin 64,
    (forwardTable2 (7936 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (7936 + m.val))).val → Listed 2 (7936 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block125 : ∀ m : Fin 64,
    (forwardTable2 (8000 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (8000 + m.val))).val → Listed 2 (8000 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block126 : ∀ m : Fin 64,
    (forwardTable2 (8064 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (8064 + m.val))).val → Listed 2 (8064 + m.val)) := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem matches2_block127 : ∀ m : Fin 64,
    (forwardTable2 (8128 + m.val) = backwardTable2 (reverseCode (Fin.ofNat 8192 (8128 + m.val))).val → Listed 2 (8128 + m.val)) := by
  decide +kernel

theorem matches2 (m : Fin 8192) :
    (forwardTable2 m.val = backwardTable2 (reverseCode (Fin.ofNat 8192 m.val)).val → Listed 2 m.val) := by
  apply check_blocks (P := fun a => (forwardTable2 a = backwardTable2 (reverseCode (Fin.ofNat 8192 a)).val → Listed 2 a))
    (size := 64) (blocks := 128) (by decide) ?_ m
  intro b
  fin_cases b
  · exact matches2_block0
  · exact matches2_block1
  · exact matches2_block2
  · exact matches2_block3
  · exact matches2_block4
  · exact matches2_block5
  · exact matches2_block6
  · exact matches2_block7
  · exact matches2_block8
  · exact matches2_block9
  · exact matches2_block10
  · exact matches2_block11
  · exact matches2_block12
  · exact matches2_block13
  · exact matches2_block14
  · exact matches2_block15
  · exact matches2_block16
  · exact matches2_block17
  · exact matches2_block18
  · exact matches2_block19
  · exact matches2_block20
  · exact matches2_block21
  · exact matches2_block22
  · exact matches2_block23
  · exact matches2_block24
  · exact matches2_block25
  · exact matches2_block26
  · exact matches2_block27
  · exact matches2_block28
  · exact matches2_block29
  · exact matches2_block30
  · exact matches2_block31
  · exact matches2_block32
  · exact matches2_block33
  · exact matches2_block34
  · exact matches2_block35
  · exact matches2_block36
  · exact matches2_block37
  · exact matches2_block38
  · exact matches2_block39
  · exact matches2_block40
  · exact matches2_block41
  · exact matches2_block42
  · exact matches2_block43
  · exact matches2_block44
  · exact matches2_block45
  · exact matches2_block46
  · exact matches2_block47
  · exact matches2_block48
  · exact matches2_block49
  · exact matches2_block50
  · exact matches2_block51
  · exact matches2_block52
  · exact matches2_block53
  · exact matches2_block54
  · exact matches2_block55
  · exact matches2_block56
  · exact matches2_block57
  · exact matches2_block58
  · exact matches2_block59
  · exact matches2_block60
  · exact matches2_block61
  · exact matches2_block62
  · exact matches2_block63
  · exact matches2_block64
  · exact matches2_block65
  · exact matches2_block66
  · exact matches2_block67
  · exact matches2_block68
  · exact matches2_block69
  · exact matches2_block70
  · exact matches2_block71
  · exact matches2_block72
  · exact matches2_block73
  · exact matches2_block74
  · exact matches2_block75
  · exact matches2_block76
  · exact matches2_block77
  · exact matches2_block78
  · exact matches2_block79
  · exact matches2_block80
  · exact matches2_block81
  · exact matches2_block82
  · exact matches2_block83
  · exact matches2_block84
  · exact matches2_block85
  · exact matches2_block86
  · exact matches2_block87
  · exact matches2_block88
  · exact matches2_block89
  · exact matches2_block90
  · exact matches2_block91
  · exact matches2_block92
  · exact matches2_block93
  · exact matches2_block94
  · exact matches2_block95
  · exact matches2_block96
  · exact matches2_block97
  · exact matches2_block98
  · exact matches2_block99
  · exact matches2_block100
  · exact matches2_block101
  · exact matches2_block102
  · exact matches2_block103
  · exact matches2_block104
  · exact matches2_block105
  · exact matches2_block106
  · exact matches2_block107
  · exact matches2_block108
  · exact matches2_block109
  · exact matches2_block110
  · exact matches2_block111
  · exact matches2_block112
  · exact matches2_block113
  · exact matches2_block114
  · exact matches2_block115
  · exact matches2_block116
  · exact matches2_block117
  · exact matches2_block118
  · exact matches2_block119
  · exact matches2_block120
  · exact matches2_block121
  · exact matches2_block122
  · exact matches2_block123
  · exact matches2_block124
  · exact matches2_block125
  · exact matches2_block126
  · exact matches2_block127


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
