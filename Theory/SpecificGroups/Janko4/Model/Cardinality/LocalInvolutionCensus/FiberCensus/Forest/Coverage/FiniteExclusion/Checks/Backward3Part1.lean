module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber3

/-!
# Reverse fiber 3, recurrence range 1

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
private theorem backward_checked3_11_block0 : ∀ m : Fin 64,
    backwardTable3 ((0 + m.val) + 2048) = backwardAction (backwardTable3 (0 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block1 : ∀ m : Fin 64,
    backwardTable3 ((64 + m.val) + 2048) = backwardAction (backwardTable3 (64 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block2 : ∀ m : Fin 64,
    backwardTable3 ((128 + m.val) + 2048) = backwardAction (backwardTable3 (128 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block3 : ∀ m : Fin 64,
    backwardTable3 ((192 + m.val) + 2048) = backwardAction (backwardTable3 (192 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block4 : ∀ m : Fin 64,
    backwardTable3 ((256 + m.val) + 2048) = backwardAction (backwardTable3 (256 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block5 : ∀ m : Fin 64,
    backwardTable3 ((320 + m.val) + 2048) = backwardAction (backwardTable3 (320 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block6 : ∀ m : Fin 64,
    backwardTable3 ((384 + m.val) + 2048) = backwardAction (backwardTable3 (384 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block7 : ∀ m : Fin 64,
    backwardTable3 ((448 + m.val) + 2048) = backwardAction (backwardTable3 (448 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block8 : ∀ m : Fin 64,
    backwardTable3 ((512 + m.val) + 2048) = backwardAction (backwardTable3 (512 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block9 : ∀ m : Fin 64,
    backwardTable3 ((576 + m.val) + 2048) = backwardAction (backwardTable3 (576 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block10 : ∀ m : Fin 64,
    backwardTable3 ((640 + m.val) + 2048) = backwardAction (backwardTable3 (640 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block11 : ∀ m : Fin 64,
    backwardTable3 ((704 + m.val) + 2048) = backwardAction (backwardTable3 (704 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block12 : ∀ m : Fin 64,
    backwardTable3 ((768 + m.val) + 2048) = backwardAction (backwardTable3 (768 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block13 : ∀ m : Fin 64,
    backwardTable3 ((832 + m.val) + 2048) = backwardAction (backwardTable3 (832 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block14 : ∀ m : Fin 64,
    backwardTable3 ((896 + m.val) + 2048) = backwardAction (backwardTable3 (896 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block15 : ∀ m : Fin 64,
    backwardTable3 ((960 + m.val) + 2048) = backwardAction (backwardTable3 (960 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block16 : ∀ m : Fin 64,
    backwardTable3 ((1024 + m.val) + 2048) = backwardAction (backwardTable3 (1024 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block17 : ∀ m : Fin 64,
    backwardTable3 ((1088 + m.val) + 2048) = backwardAction (backwardTable3 (1088 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block18 : ∀ m : Fin 64,
    backwardTable3 ((1152 + m.val) + 2048) = backwardAction (backwardTable3 (1152 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block19 : ∀ m : Fin 64,
    backwardTable3 ((1216 + m.val) + 2048) = backwardAction (backwardTable3 (1216 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block20 : ∀ m : Fin 64,
    backwardTable3 ((1280 + m.val) + 2048) = backwardAction (backwardTable3 (1280 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block21 : ∀ m : Fin 64,
    backwardTable3 ((1344 + m.val) + 2048) = backwardAction (backwardTable3 (1344 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block22 : ∀ m : Fin 64,
    backwardTable3 ((1408 + m.val) + 2048) = backwardAction (backwardTable3 (1408 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block23 : ∀ m : Fin 64,
    backwardTable3 ((1472 + m.val) + 2048) = backwardAction (backwardTable3 (1472 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block24 : ∀ m : Fin 64,
    backwardTable3 ((1536 + m.val) + 2048) = backwardAction (backwardTable3 (1536 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block25 : ∀ m : Fin 64,
    backwardTable3 ((1600 + m.val) + 2048) = backwardAction (backwardTable3 (1600 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block26 : ∀ m : Fin 64,
    backwardTable3 ((1664 + m.val) + 2048) = backwardAction (backwardTable3 (1664 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block27 : ∀ m : Fin 64,
    backwardTable3 ((1728 + m.val) + 2048) = backwardAction (backwardTable3 (1728 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block28 : ∀ m : Fin 64,
    backwardTable3 ((1792 + m.val) + 2048) = backwardAction (backwardTable3 (1792 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block29 : ∀ m : Fin 64,
    backwardTable3 ((1856 + m.val) + 2048) = backwardAction (backwardTable3 (1856 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block30 : ∀ m : Fin 64,
    backwardTable3 ((1920 + m.val) + 2048) = backwardAction (backwardTable3 (1920 + m.val)) 11 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem backward_checked3_11_block31 : ∀ m : Fin 64,
    backwardTable3 ((1984 + m.val) + 2048) = backwardAction (backwardTable3 (1984 + m.val)) 11 := by
  decide +kernel

theorem backward_checked3_11 (m : Fin 2048) :
    backwardTable3 (m.val + 2048) = backwardAction (backwardTable3 m.val) 11 := by
  apply check_blocks (P := fun a => backwardTable3 (a + 2048) = backwardAction (backwardTable3 a) 11)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact backward_checked3_11_block0
  · exact backward_checked3_11_block1
  · exact backward_checked3_11_block2
  · exact backward_checked3_11_block3
  · exact backward_checked3_11_block4
  · exact backward_checked3_11_block5
  · exact backward_checked3_11_block6
  · exact backward_checked3_11_block7
  · exact backward_checked3_11_block8
  · exact backward_checked3_11_block9
  · exact backward_checked3_11_block10
  · exact backward_checked3_11_block11
  · exact backward_checked3_11_block12
  · exact backward_checked3_11_block13
  · exact backward_checked3_11_block14
  · exact backward_checked3_11_block15
  · exact backward_checked3_11_block16
  · exact backward_checked3_11_block17
  · exact backward_checked3_11_block18
  · exact backward_checked3_11_block19
  · exact backward_checked3_11_block20
  · exact backward_checked3_11_block21
  · exact backward_checked3_11_block22
  · exact backward_checked3_11_block23
  · exact backward_checked3_11_block24
  · exact backward_checked3_11_block25
  · exact backward_checked3_11_block26
  · exact backward_checked3_11_block27
  · exact backward_checked3_11_block28
  · exact backward_checked3_11_block29
  · exact backward_checked3_11_block30
  · exact backward_checked3_11_block31


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
