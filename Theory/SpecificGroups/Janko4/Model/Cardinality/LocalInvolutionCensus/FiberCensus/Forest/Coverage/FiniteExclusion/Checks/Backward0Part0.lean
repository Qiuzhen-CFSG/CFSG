module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber0

/-!
# Reverse fiber 0, recurrence range 0

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
theorem backward_checked0_0 : ∀ m : Fin 1,
    backwardTable0 (m.val + 1) = backwardAction (backwardTable0 m.val) 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_1 : ∀ m : Fin 2,
    backwardTable0 (m.val + 2) = backwardAction (backwardTable0 m.val) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_2 : ∀ m : Fin 4,
    backwardTable0 (m.val + 4) = backwardAction (backwardTable0 m.val) 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_3 : ∀ m : Fin 8,
    backwardTable0 (m.val + 8) = backwardAction (backwardTable0 m.val) 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_4 : ∀ m : Fin 16,
    backwardTable0 (m.val + 16) = backwardAction (backwardTable0 m.val) 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_5 : ∀ m : Fin 32,
    backwardTable0 (m.val + 32) = backwardAction (backwardTable0 m.val) 5 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked0_6 : ∀ m : Fin 64,
    backwardTable0 (m.val + 64) = backwardAction (backwardTable0 m.val) 6 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_7_block0 : ∀ m : Fin 64,
    backwardTable0 ((0 + m.val) + 128) = backwardAction (backwardTable0 (0 + m.val)) 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_7_block1 : ∀ m : Fin 64,
    backwardTable0 ((64 + m.val) + 128) = backwardAction (backwardTable0 (64 + m.val)) 7 := by
  decide +kernel

theorem backward_checked0_7 (m : Fin 128) :
    backwardTable0 (m.val + 128) = backwardAction (backwardTable0 m.val) 7 := by
  apply check_blocks (P := fun a => backwardTable0 (a + 128) = backwardAction (backwardTable0 a) 7)
    (size := 64) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked0_7_block0
  · exact backward_checked0_7_block1

set_option maxRecDepth 10000 in
private theorem backward_checked0_8_block0 : ∀ m : Fin 64,
    backwardTable0 ((0 + m.val) + 256) = backwardAction (backwardTable0 (0 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_8_block1 : ∀ m : Fin 64,
    backwardTable0 ((64 + m.val) + 256) = backwardAction (backwardTable0 (64 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_8_block2 : ∀ m : Fin 64,
    backwardTable0 ((128 + m.val) + 256) = backwardAction (backwardTable0 (128 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_8_block3 : ∀ m : Fin 64,
    backwardTable0 ((192 + m.val) + 256) = backwardAction (backwardTable0 (192 + m.val)) 8 := by
  decide +kernel

theorem backward_checked0_8 (m : Fin 256) :
    backwardTable0 (m.val + 256) = backwardAction (backwardTable0 m.val) 8 := by
  apply check_blocks (P := fun a => backwardTable0 (a + 256) = backwardAction (backwardTable0 a) 8)
    (size := 64) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked0_8_block0
  · exact backward_checked0_8_block1
  · exact backward_checked0_8_block2
  · exact backward_checked0_8_block3

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block0 : ∀ m : Fin 64,
    backwardTable0 ((0 + m.val) + 512) = backwardAction (backwardTable0 (0 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block1 : ∀ m : Fin 64,
    backwardTable0 ((64 + m.val) + 512) = backwardAction (backwardTable0 (64 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block2 : ∀ m : Fin 64,
    backwardTable0 ((128 + m.val) + 512) = backwardAction (backwardTable0 (128 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block3 : ∀ m : Fin 64,
    backwardTable0 ((192 + m.val) + 512) = backwardAction (backwardTable0 (192 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block4 : ∀ m : Fin 64,
    backwardTable0 ((256 + m.val) + 512) = backwardAction (backwardTable0 (256 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block5 : ∀ m : Fin 64,
    backwardTable0 ((320 + m.val) + 512) = backwardAction (backwardTable0 (320 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block6 : ∀ m : Fin 64,
    backwardTable0 ((384 + m.val) + 512) = backwardAction (backwardTable0 (384 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_9_block7 : ∀ m : Fin 64,
    backwardTable0 ((448 + m.val) + 512) = backwardAction (backwardTable0 (448 + m.val)) 9 := by
  decide +kernel

theorem backward_checked0_9 (m : Fin 512) :
    backwardTable0 (m.val + 512) = backwardAction (backwardTable0 m.val) 9 := by
  apply check_blocks (P := fun a => backwardTable0 (a + 512) = backwardAction (backwardTable0 a) 9)
    (size := 64) (blocks := 8) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked0_9_block0
  · exact backward_checked0_9_block1
  · exact backward_checked0_9_block2
  · exact backward_checked0_9_block3
  · exact backward_checked0_9_block4
  · exact backward_checked0_9_block5
  · exact backward_checked0_9_block6
  · exact backward_checked0_9_block7

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block0 : ∀ m : Fin 64,
    backwardTable0 ((0 + m.val) + 1024) = backwardAction (backwardTable0 (0 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block1 : ∀ m : Fin 64,
    backwardTable0 ((64 + m.val) + 1024) = backwardAction (backwardTable0 (64 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block2 : ∀ m : Fin 64,
    backwardTable0 ((128 + m.val) + 1024) = backwardAction (backwardTable0 (128 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block3 : ∀ m : Fin 64,
    backwardTable0 ((192 + m.val) + 1024) = backwardAction (backwardTable0 (192 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block4 : ∀ m : Fin 64,
    backwardTable0 ((256 + m.val) + 1024) = backwardAction (backwardTable0 (256 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block5 : ∀ m : Fin 64,
    backwardTable0 ((320 + m.val) + 1024) = backwardAction (backwardTable0 (320 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block6 : ∀ m : Fin 64,
    backwardTable0 ((384 + m.val) + 1024) = backwardAction (backwardTable0 (384 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block7 : ∀ m : Fin 64,
    backwardTable0 ((448 + m.val) + 1024) = backwardAction (backwardTable0 (448 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block8 : ∀ m : Fin 64,
    backwardTable0 ((512 + m.val) + 1024) = backwardAction (backwardTable0 (512 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block9 : ∀ m : Fin 64,
    backwardTable0 ((576 + m.val) + 1024) = backwardAction (backwardTable0 (576 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block10 : ∀ m : Fin 64,
    backwardTable0 ((640 + m.val) + 1024) = backwardAction (backwardTable0 (640 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block11 : ∀ m : Fin 64,
    backwardTable0 ((704 + m.val) + 1024) = backwardAction (backwardTable0 (704 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block12 : ∀ m : Fin 64,
    backwardTable0 ((768 + m.val) + 1024) = backwardAction (backwardTable0 (768 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block13 : ∀ m : Fin 64,
    backwardTable0 ((832 + m.val) + 1024) = backwardAction (backwardTable0 (832 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block14 : ∀ m : Fin 64,
    backwardTable0 ((896 + m.val) + 1024) = backwardAction (backwardTable0 (896 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked0_10_block15 : ∀ m : Fin 64,
    backwardTable0 ((960 + m.val) + 1024) = backwardAction (backwardTable0 (960 + m.val)) 10 := by
  decide +kernel

theorem backward_checked0_10 (m : Fin 1024) :
    backwardTable0 (m.val + 1024) = backwardAction (backwardTable0 m.val) 10 := by
  apply check_blocks (P := fun a => backwardTable0 (a + 1024) = backwardAction (backwardTable0 a) 10)
    (size := 64) (blocks := 16) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked0_10_block0
  · exact backward_checked0_10_block1
  · exact backward_checked0_10_block2
  · exact backward_checked0_10_block3
  · exact backward_checked0_10_block4
  · exact backward_checked0_10_block5
  · exact backward_checked0_10_block6
  · exact backward_checked0_10_block7
  · exact backward_checked0_10_block8
  · exact backward_checked0_10_block9
  · exact backward_checked0_10_block10
  · exact backward_checked0_10_block11
  · exact backward_checked0_10_block12
  · exact backward_checked0_10_block13
  · exact backward_checked0_10_block14
  · exact backward_checked0_10_block15


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
