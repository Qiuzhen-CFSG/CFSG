module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward0

/-!
# Forward fiber 1, coordinate range 0

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
private theorem forward_checked1_part0_block0 : ∀ m : Fin 64,
    forwardTable1 (0 + (0 + m.val)) = forwardAction (forwardTable0 (0 + (0 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block1 : ∀ m : Fin 64,
    forwardTable1 (0 + (64 + m.val)) = forwardAction (forwardTable0 (0 + (64 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block2 : ∀ m : Fin 64,
    forwardTable1 (0 + (128 + m.val)) = forwardAction (forwardTable0 (0 + (128 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block3 : ∀ m : Fin 64,
    forwardTable1 (0 + (192 + m.val)) = forwardAction (forwardTable0 (0 + (192 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block4 : ∀ m : Fin 64,
    forwardTable1 (0 + (256 + m.val)) = forwardAction (forwardTable0 (0 + (256 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block5 : ∀ m : Fin 64,
    forwardTable1 (0 + (320 + m.val)) = forwardAction (forwardTable0 (0 + (320 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block6 : ∀ m : Fin 64,
    forwardTable1 (0 + (384 + m.val)) = forwardAction (forwardTable0 (0 + (384 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block7 : ∀ m : Fin 64,
    forwardTable1 (0 + (448 + m.val)) = forwardAction (forwardTable0 (0 + (448 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block8 : ∀ m : Fin 64,
    forwardTable1 (0 + (512 + m.val)) = forwardAction (forwardTable0 (0 + (512 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block9 : ∀ m : Fin 64,
    forwardTable1 (0 + (576 + m.val)) = forwardAction (forwardTable0 (0 + (576 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block10 : ∀ m : Fin 64,
    forwardTable1 (0 + (640 + m.val)) = forwardAction (forwardTable0 (0 + (640 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block11 : ∀ m : Fin 64,
    forwardTable1 (0 + (704 + m.val)) = forwardAction (forwardTable0 (0 + (704 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block12 : ∀ m : Fin 64,
    forwardTable1 (0 + (768 + m.val)) = forwardAction (forwardTable0 (0 + (768 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block13 : ∀ m : Fin 64,
    forwardTable1 (0 + (832 + m.val)) = forwardAction (forwardTable0 (0 + (832 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block14 : ∀ m : Fin 64,
    forwardTable1 (0 + (896 + m.val)) = forwardAction (forwardTable0 (0 + (896 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block15 : ∀ m : Fin 64,
    forwardTable1 (0 + (960 + m.val)) = forwardAction (forwardTable0 (0 + (960 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block16 : ∀ m : Fin 64,
    forwardTable1 (0 + (1024 + m.val)) = forwardAction (forwardTable0 (0 + (1024 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block17 : ∀ m : Fin 64,
    forwardTable1 (0 + (1088 + m.val)) = forwardAction (forwardTable0 (0 + (1088 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block18 : ∀ m : Fin 64,
    forwardTable1 (0 + (1152 + m.val)) = forwardAction (forwardTable0 (0 + (1152 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block19 : ∀ m : Fin 64,
    forwardTable1 (0 + (1216 + m.val)) = forwardAction (forwardTable0 (0 + (1216 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block20 : ∀ m : Fin 64,
    forwardTable1 (0 + (1280 + m.val)) = forwardAction (forwardTable0 (0 + (1280 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block21 : ∀ m : Fin 64,
    forwardTable1 (0 + (1344 + m.val)) = forwardAction (forwardTable0 (0 + (1344 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block22 : ∀ m : Fin 64,
    forwardTable1 (0 + (1408 + m.val)) = forwardAction (forwardTable0 (0 + (1408 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block23 : ∀ m : Fin 64,
    forwardTable1 (0 + (1472 + m.val)) = forwardAction (forwardTable0 (0 + (1472 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block24 : ∀ m : Fin 64,
    forwardTable1 (0 + (1536 + m.val)) = forwardAction (forwardTable0 (0 + (1536 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block25 : ∀ m : Fin 64,
    forwardTable1 (0 + (1600 + m.val)) = forwardAction (forwardTable0 (0 + (1600 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block26 : ∀ m : Fin 64,
    forwardTable1 (0 + (1664 + m.val)) = forwardAction (forwardTable0 (0 + (1664 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block27 : ∀ m : Fin 64,
    forwardTable1 (0 + (1728 + m.val)) = forwardAction (forwardTable0 (0 + (1728 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block28 : ∀ m : Fin 64,
    forwardTable1 (0 + (1792 + m.val)) = forwardAction (forwardTable0 (0 + (1792 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block29 : ∀ m : Fin 64,
    forwardTable1 (0 + (1856 + m.val)) = forwardAction (forwardTable0 (0 + (1856 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block30 : ∀ m : Fin 64,
    forwardTable1 (0 + (1920 + m.val)) = forwardAction (forwardTable0 (0 + (1920 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part0_block31 : ∀ m : Fin 64,
    forwardTable1 (0 + (1984 + m.val)) = forwardAction (forwardTable0 (0 + (1984 + m.val))) 1 := by
  decide +kernel

theorem forward_checked1_part0 (m : Fin 2048) :
    forwardTable1 (0 + m.val) = forwardAction (forwardTable0 (0 + m.val)) 1 := by
  apply check_blocks (P := fun a => forwardTable1 (0 + a) = forwardAction (forwardTable0 (0 + a)) 1)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact forward_checked1_part0_block0
  · exact forward_checked1_part0_block1
  · exact forward_checked1_part0_block2
  · exact forward_checked1_part0_block3
  · exact forward_checked1_part0_block4
  · exact forward_checked1_part0_block5
  · exact forward_checked1_part0_block6
  · exact forward_checked1_part0_block7
  · exact forward_checked1_part0_block8
  · exact forward_checked1_part0_block9
  · exact forward_checked1_part0_block10
  · exact forward_checked1_part0_block11
  · exact forward_checked1_part0_block12
  · exact forward_checked1_part0_block13
  · exact forward_checked1_part0_block14
  · exact forward_checked1_part0_block15
  · exact forward_checked1_part0_block16
  · exact forward_checked1_part0_block17
  · exact forward_checked1_part0_block18
  · exact forward_checked1_part0_block19
  · exact forward_checked1_part0_block20
  · exact forward_checked1_part0_block21
  · exact forward_checked1_part0_block22
  · exact forward_checked1_part0_block23
  · exact forward_checked1_part0_block24
  · exact forward_checked1_part0_block25
  · exact forward_checked1_part0_block26
  · exact forward_checked1_part0_block27
  · exact forward_checked1_part0_block28
  · exact forward_checked1_part0_block29
  · exact forward_checked1_part0_block30
  · exact forward_checked1_part0_block31


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
