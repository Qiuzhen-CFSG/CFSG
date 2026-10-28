module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber2

/-!
# Reverse fiber 2, recurrence range 3

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
private theorem backward_checked2_12_part1_block0 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (0 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (0 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block1 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (64 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (64 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block2 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (128 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (128 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block3 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (192 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (192 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block4 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (256 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (256 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block5 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (320 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (320 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block6 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (384 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (384 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block7 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (448 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (448 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block8 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (512 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (512 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block9 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (576 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (576 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block10 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (640 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (640 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block11 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (704 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (704 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block12 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (768 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (768 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block13 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (832 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (832 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block14 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (896 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (896 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block15 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (960 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (960 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block16 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1024 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1024 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block17 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1088 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1088 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block18 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1152 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1152 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block19 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1216 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1216 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block20 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1280 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1280 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block21 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1344 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1344 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block22 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1408 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1408 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block23 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1472 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1472 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block24 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1536 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1536 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block25 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1600 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1600 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block26 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1664 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1664 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block27 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1728 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1728 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block28 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1792 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1792 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block29 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1856 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1856 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block30 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1920 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1920 + m.val))) 12 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked2_12_part1_block31 : ∀ m : Fin 64,
    backwardTable2 ((2048 + (1984 + m.val)) + 4096) = backwardAction (backwardTable2 (2048 + (1984 + m.val))) 12 := by
  decide +kernel

theorem backward_checked2_12_part1 (m : Fin 2048) :
    backwardTable2 ((2048 + m.val) + 4096) = backwardAction (backwardTable2 (2048 + m.val)) 12 := by
  apply check_blocks (P := fun a => backwardTable2 ((2048 + a) + 4096) = backwardAction (backwardTable2 (2048 + a)) 12)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked2_12_part1_block0
  · exact backward_checked2_12_part1_block1
  · exact backward_checked2_12_part1_block2
  · exact backward_checked2_12_part1_block3
  · exact backward_checked2_12_part1_block4
  · exact backward_checked2_12_part1_block5
  · exact backward_checked2_12_part1_block6
  · exact backward_checked2_12_part1_block7
  · exact backward_checked2_12_part1_block8
  · exact backward_checked2_12_part1_block9
  · exact backward_checked2_12_part1_block10
  · exact backward_checked2_12_part1_block11
  · exact backward_checked2_12_part1_block12
  · exact backward_checked2_12_part1_block13
  · exact backward_checked2_12_part1_block14
  · exact backward_checked2_12_part1_block15
  · exact backward_checked2_12_part1_block16
  · exact backward_checked2_12_part1_block17
  · exact backward_checked2_12_part1_block18
  · exact backward_checked2_12_part1_block19
  · exact backward_checked2_12_part1_block20
  · exact backward_checked2_12_part1_block21
  · exact backward_checked2_12_part1_block22
  · exact backward_checked2_12_part1_block23
  · exact backward_checked2_12_part1_block24
  · exact backward_checked2_12_part1_block25
  · exact backward_checked2_12_part1_block26
  · exact backward_checked2_12_part1_block27
  · exact backward_checked2_12_part1_block28
  · exact backward_checked2_12_part1_block29
  · exact backward_checked2_12_part1_block30
  · exact backward_checked2_12_part1_block31


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
