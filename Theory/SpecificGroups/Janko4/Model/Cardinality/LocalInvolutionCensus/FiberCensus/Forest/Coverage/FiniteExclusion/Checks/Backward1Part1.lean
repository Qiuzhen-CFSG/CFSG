module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber1

/-!
# Reverse fiber 1, recurrence range 1

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
private theorem backward_checked1_11_block0 : ∀ m : Fin 64,
    backwardTable1 ((0 + m.val) + 2048) = backwardAction (backwardTable1 (0 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block1 : ∀ m : Fin 64,
    backwardTable1 ((64 + m.val) + 2048) = backwardAction (backwardTable1 (64 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block2 : ∀ m : Fin 64,
    backwardTable1 ((128 + m.val) + 2048) = backwardAction (backwardTable1 (128 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block3 : ∀ m : Fin 64,
    backwardTable1 ((192 + m.val) + 2048) = backwardAction (backwardTable1 (192 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block4 : ∀ m : Fin 64,
    backwardTable1 ((256 + m.val) + 2048) = backwardAction (backwardTable1 (256 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block5 : ∀ m : Fin 64,
    backwardTable1 ((320 + m.val) + 2048) = backwardAction (backwardTable1 (320 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block6 : ∀ m : Fin 64,
    backwardTable1 ((384 + m.val) + 2048) = backwardAction (backwardTable1 (384 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block7 : ∀ m : Fin 64,
    backwardTable1 ((448 + m.val) + 2048) = backwardAction (backwardTable1 (448 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block8 : ∀ m : Fin 64,
    backwardTable1 ((512 + m.val) + 2048) = backwardAction (backwardTable1 (512 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block9 : ∀ m : Fin 64,
    backwardTable1 ((576 + m.val) + 2048) = backwardAction (backwardTable1 (576 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block10 : ∀ m : Fin 64,
    backwardTable1 ((640 + m.val) + 2048) = backwardAction (backwardTable1 (640 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block11 : ∀ m : Fin 64,
    backwardTable1 ((704 + m.val) + 2048) = backwardAction (backwardTable1 (704 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block12 : ∀ m : Fin 64,
    backwardTable1 ((768 + m.val) + 2048) = backwardAction (backwardTable1 (768 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block13 : ∀ m : Fin 64,
    backwardTable1 ((832 + m.val) + 2048) = backwardAction (backwardTable1 (832 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block14 : ∀ m : Fin 64,
    backwardTable1 ((896 + m.val) + 2048) = backwardAction (backwardTable1 (896 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block15 : ∀ m : Fin 64,
    backwardTable1 ((960 + m.val) + 2048) = backwardAction (backwardTable1 (960 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block16 : ∀ m : Fin 64,
    backwardTable1 ((1024 + m.val) + 2048) = backwardAction (backwardTable1 (1024 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block17 : ∀ m : Fin 64,
    backwardTable1 ((1088 + m.val) + 2048) = backwardAction (backwardTable1 (1088 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block18 : ∀ m : Fin 64,
    backwardTable1 ((1152 + m.val) + 2048) = backwardAction (backwardTable1 (1152 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block19 : ∀ m : Fin 64,
    backwardTable1 ((1216 + m.val) + 2048) = backwardAction (backwardTable1 (1216 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block20 : ∀ m : Fin 64,
    backwardTable1 ((1280 + m.val) + 2048) = backwardAction (backwardTable1 (1280 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block21 : ∀ m : Fin 64,
    backwardTable1 ((1344 + m.val) + 2048) = backwardAction (backwardTable1 (1344 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block22 : ∀ m : Fin 64,
    backwardTable1 ((1408 + m.val) + 2048) = backwardAction (backwardTable1 (1408 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block23 : ∀ m : Fin 64,
    backwardTable1 ((1472 + m.val) + 2048) = backwardAction (backwardTable1 (1472 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block24 : ∀ m : Fin 64,
    backwardTable1 ((1536 + m.val) + 2048) = backwardAction (backwardTable1 (1536 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block25 : ∀ m : Fin 64,
    backwardTable1 ((1600 + m.val) + 2048) = backwardAction (backwardTable1 (1600 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block26 : ∀ m : Fin 64,
    backwardTable1 ((1664 + m.val) + 2048) = backwardAction (backwardTable1 (1664 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block27 : ∀ m : Fin 64,
    backwardTable1 ((1728 + m.val) + 2048) = backwardAction (backwardTable1 (1728 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block28 : ∀ m : Fin 64,
    backwardTable1 ((1792 + m.val) + 2048) = backwardAction (backwardTable1 (1792 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block29 : ∀ m : Fin 64,
    backwardTable1 ((1856 + m.val) + 2048) = backwardAction (backwardTable1 (1856 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block30 : ∀ m : Fin 64,
    backwardTable1 ((1920 + m.val) + 2048) = backwardAction (backwardTable1 (1920 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked1_11_block31 : ∀ m : Fin 64,
    backwardTable1 ((1984 + m.val) + 2048) = backwardAction (backwardTable1 (1984 + m.val)) 11 := by
  decide +kernel

theorem backward_checked1_11 (m : Fin 2048) :
    backwardTable1 (m.val + 2048) = backwardAction (backwardTable1 m.val) 11 := by
  apply check_blocks (P := fun a => backwardTable1 (a + 2048) = backwardAction (backwardTable1 a) 11)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked1_11_block0
  · exact backward_checked1_11_block1
  · exact backward_checked1_11_block2
  · exact backward_checked1_11_block3
  · exact backward_checked1_11_block4
  · exact backward_checked1_11_block5
  · exact backward_checked1_11_block6
  · exact backward_checked1_11_block7
  · exact backward_checked1_11_block8
  · exact backward_checked1_11_block9
  · exact backward_checked1_11_block10
  · exact backward_checked1_11_block11
  · exact backward_checked1_11_block12
  · exact backward_checked1_11_block13
  · exact backward_checked1_11_block14
  · exact backward_checked1_11_block15
  · exact backward_checked1_11_block16
  · exact backward_checked1_11_block17
  · exact backward_checked1_11_block18
  · exact backward_checked1_11_block19
  · exact backward_checked1_11_block20
  · exact backward_checked1_11_block21
  · exact backward_checked1_11_block22
  · exact backward_checked1_11_block23
  · exact backward_checked1_11_block24
  · exact backward_checked1_11_block25
  · exact backward_checked1_11_block26
  · exact backward_checked1_11_block27
  · exact backward_checked1_11_block28
  · exact backward_checked1_11_block29
  · exact backward_checked1_11_block30
  · exact backward_checked1_11_block31


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
