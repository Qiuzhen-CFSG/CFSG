module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber2

/-!
# Reverse fiber 2, recurrence range 0

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
theorem backward_checked2_0 : ∀ m : Fin 1,
    backwardTable2 (m.val + 1) = backwardAction (backwardTable2 m.val) 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_1 : ∀ m : Fin 2,
    backwardTable2 (m.val + 2) = backwardAction (backwardTable2 m.val) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_2 : ∀ m : Fin 4,
    backwardTable2 (m.val + 4) = backwardAction (backwardTable2 m.val) 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_3 : ∀ m : Fin 8,
    backwardTable2 (m.val + 8) = backwardAction (backwardTable2 m.val) 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_4 : ∀ m : Fin 16,
    backwardTable2 (m.val + 16) = backwardAction (backwardTable2 m.val) 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_5 : ∀ m : Fin 32,
    backwardTable2 (m.val + 32) = backwardAction (backwardTable2 m.val) 5 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem backward_checked2_6 : ∀ m : Fin 64,
    backwardTable2 (m.val + 64) = backwardAction (backwardTable2 m.val) 6 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_7_block0 : ∀ m : Fin 64,
    backwardTable2 ((0 + m.val) + 128) = backwardAction (backwardTable2 (0 + m.val)) 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_7_block1 : ∀ m : Fin 64,
    backwardTable2 ((64 + m.val) + 128) = backwardAction (backwardTable2 (64 + m.val)) 7 := by
  decide +kernel

theorem backward_checked2_7 (m : Fin 128) :
    backwardTable2 (m.val + 128) = backwardAction (backwardTable2 m.val) 7 := by
  apply check_blocks (P := fun a => backwardTable2 (a + 128) = backwardAction (backwardTable2 a) 7)
    (size := 64) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_7_block0
  · exact backward_checked2_7_block1

set_option maxRecDepth 10000 in
private theorem backward_checked2_8_block0 : ∀ m : Fin 64,
    backwardTable2 ((0 + m.val) + 256) = backwardAction (backwardTable2 (0 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_8_block1 : ∀ m : Fin 64,
    backwardTable2 ((64 + m.val) + 256) = backwardAction (backwardTable2 (64 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_8_block2 : ∀ m : Fin 64,
    backwardTable2 ((128 + m.val) + 256) = backwardAction (backwardTable2 (128 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_8_block3 : ∀ m : Fin 64,
    backwardTable2 ((192 + m.val) + 256) = backwardAction (backwardTable2 (192 + m.val)) 8 := by
  decide +kernel

theorem backward_checked2_8 (m : Fin 256) :
    backwardTable2 (m.val + 256) = backwardAction (backwardTable2 m.val) 8 := by
  apply check_blocks (P := fun a => backwardTable2 (a + 256) = backwardAction (backwardTable2 a) 8)
    (size := 64) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_8_block0
  · exact backward_checked2_8_block1
  · exact backward_checked2_8_block2
  · exact backward_checked2_8_block3

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block0 : ∀ m : Fin 64,
    backwardTable2 ((0 + m.val) + 512) = backwardAction (backwardTable2 (0 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block1 : ∀ m : Fin 64,
    backwardTable2 ((64 + m.val) + 512) = backwardAction (backwardTable2 (64 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block2 : ∀ m : Fin 64,
    backwardTable2 ((128 + m.val) + 512) = backwardAction (backwardTable2 (128 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block3 : ∀ m : Fin 64,
    backwardTable2 ((192 + m.val) + 512) = backwardAction (backwardTable2 (192 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block4 : ∀ m : Fin 64,
    backwardTable2 ((256 + m.val) + 512) = backwardAction (backwardTable2 (256 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block5 : ∀ m : Fin 64,
    backwardTable2 ((320 + m.val) + 512) = backwardAction (backwardTable2 (320 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block6 : ∀ m : Fin 64,
    backwardTable2 ((384 + m.val) + 512) = backwardAction (backwardTable2 (384 + m.val)) 9 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_9_block7 : ∀ m : Fin 64,
    backwardTable2 ((448 + m.val) + 512) = backwardAction (backwardTable2 (448 + m.val)) 9 := by
  decide +kernel

theorem backward_checked2_9 (m : Fin 512) :
    backwardTable2 (m.val + 512) = backwardAction (backwardTable2 m.val) 9 := by
  apply check_blocks (P := fun a => backwardTable2 (a + 512) = backwardAction (backwardTable2 a) 9)
    (size := 64) (blocks := 8) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_9_block0
  · exact backward_checked2_9_block1
  · exact backward_checked2_9_block2
  · exact backward_checked2_9_block3
  · exact backward_checked2_9_block4
  · exact backward_checked2_9_block5
  · exact backward_checked2_9_block6
  · exact backward_checked2_9_block7

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block0 : ∀ m : Fin 64,
    backwardTable2 ((0 + m.val) + 1024) = backwardAction (backwardTable2 (0 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block1 : ∀ m : Fin 64,
    backwardTable2 ((64 + m.val) + 1024) = backwardAction (backwardTable2 (64 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block2 : ∀ m : Fin 64,
    backwardTable2 ((128 + m.val) + 1024) = backwardAction (backwardTable2 (128 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block3 : ∀ m : Fin 64,
    backwardTable2 ((192 + m.val) + 1024) = backwardAction (backwardTable2 (192 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block4 : ∀ m : Fin 64,
    backwardTable2 ((256 + m.val) + 1024) = backwardAction (backwardTable2 (256 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block5 : ∀ m : Fin 64,
    backwardTable2 ((320 + m.val) + 1024) = backwardAction (backwardTable2 (320 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block6 : ∀ m : Fin 64,
    backwardTable2 ((384 + m.val) + 1024) = backwardAction (backwardTable2 (384 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block7 : ∀ m : Fin 64,
    backwardTable2 ((448 + m.val) + 1024) = backwardAction (backwardTable2 (448 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block8 : ∀ m : Fin 64,
    backwardTable2 ((512 + m.val) + 1024) = backwardAction (backwardTable2 (512 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block9 : ∀ m : Fin 64,
    backwardTable2 ((576 + m.val) + 1024) = backwardAction (backwardTable2 (576 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block10 : ∀ m : Fin 64,
    backwardTable2 ((640 + m.val) + 1024) = backwardAction (backwardTable2 (640 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block11 : ∀ m : Fin 64,
    backwardTable2 ((704 + m.val) + 1024) = backwardAction (backwardTable2 (704 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block12 : ∀ m : Fin 64,
    backwardTable2 ((768 + m.val) + 1024) = backwardAction (backwardTable2 (768 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block13 : ∀ m : Fin 64,
    backwardTable2 ((832 + m.val) + 1024) = backwardAction (backwardTable2 (832 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block14 : ∀ m : Fin 64,
    backwardTable2 ((896 + m.val) + 1024) = backwardAction (backwardTable2 (896 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_10_block15 : ∀ m : Fin 64,
    backwardTable2 ((960 + m.val) + 1024) = backwardAction (backwardTable2 (960 + m.val)) 10 := by
  decide +kernel

theorem backward_checked2_10 (m : Fin 1024) :
    backwardTable2 (m.val + 1024) = backwardAction (backwardTable2 m.val) 10 := by
  apply check_blocks (P := fun a => backwardTable2 (a + 1024) = backwardAction (backwardTable2 a) 10)
    (size := 64) (blocks := 16) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_10_block0
  · exact backward_checked2_10_block1
  · exact backward_checked2_10_block2
  · exact backward_checked2_10_block3
  · exact backward_checked2_10_block4
  · exact backward_checked2_10_block5
  · exact backward_checked2_10_block6
  · exact backward_checked2_10_block7
  · exact backward_checked2_10_block8
  · exact backward_checked2_10_block9
  · exact backward_checked2_10_block10
  · exact backward_checked2_10_block11
  · exact backward_checked2_10_block12
  · exact backward_checked2_10_block13
  · exact backward_checked2_10_block14
  · exact backward_checked2_10_block15


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
