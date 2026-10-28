module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Tables.Fiber1
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Forward0

/-!
# Forward fiber 1, coordinate range 2

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
private theorem forward_checked1_part2_block0 : ∀ m : Fin 64,
    forwardTable1 (4096 + (0 + m.val)) = forwardAction (forwardTable0 (4096 + (0 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block1 : ∀ m : Fin 64,
    forwardTable1 (4096 + (64 + m.val)) = forwardAction (forwardTable0 (4096 + (64 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block2 : ∀ m : Fin 64,
    forwardTable1 (4096 + (128 + m.val)) = forwardAction (forwardTable0 (4096 + (128 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block3 : ∀ m : Fin 64,
    forwardTable1 (4096 + (192 + m.val)) = forwardAction (forwardTable0 (4096 + (192 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block4 : ∀ m : Fin 64,
    forwardTable1 (4096 + (256 + m.val)) = forwardAction (forwardTable0 (4096 + (256 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block5 : ∀ m : Fin 64,
    forwardTable1 (4096 + (320 + m.val)) = forwardAction (forwardTable0 (4096 + (320 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block6 : ∀ m : Fin 64,
    forwardTable1 (4096 + (384 + m.val)) = forwardAction (forwardTable0 (4096 + (384 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block7 : ∀ m : Fin 64,
    forwardTable1 (4096 + (448 + m.val)) = forwardAction (forwardTable0 (4096 + (448 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block8 : ∀ m : Fin 64,
    forwardTable1 (4096 + (512 + m.val)) = forwardAction (forwardTable0 (4096 + (512 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block9 : ∀ m : Fin 64,
    forwardTable1 (4096 + (576 + m.val)) = forwardAction (forwardTable0 (4096 + (576 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block10 : ∀ m : Fin 64,
    forwardTable1 (4096 + (640 + m.val)) = forwardAction (forwardTable0 (4096 + (640 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block11 : ∀ m : Fin 64,
    forwardTable1 (4096 + (704 + m.val)) = forwardAction (forwardTable0 (4096 + (704 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block12 : ∀ m : Fin 64,
    forwardTable1 (4096 + (768 + m.val)) = forwardAction (forwardTable0 (4096 + (768 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block13 : ∀ m : Fin 64,
    forwardTable1 (4096 + (832 + m.val)) = forwardAction (forwardTable0 (4096 + (832 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block14 : ∀ m : Fin 64,
    forwardTable1 (4096 + (896 + m.val)) = forwardAction (forwardTable0 (4096 + (896 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block15 : ∀ m : Fin 64,
    forwardTable1 (4096 + (960 + m.val)) = forwardAction (forwardTable0 (4096 + (960 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block16 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1024 + m.val)) = forwardAction (forwardTable0 (4096 + (1024 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block17 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1088 + m.val)) = forwardAction (forwardTable0 (4096 + (1088 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block18 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1152 + m.val)) = forwardAction (forwardTable0 (4096 + (1152 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block19 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1216 + m.val)) = forwardAction (forwardTable0 (4096 + (1216 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block20 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1280 + m.val)) = forwardAction (forwardTable0 (4096 + (1280 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block21 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1344 + m.val)) = forwardAction (forwardTable0 (4096 + (1344 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block22 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1408 + m.val)) = forwardAction (forwardTable0 (4096 + (1408 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block23 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1472 + m.val)) = forwardAction (forwardTable0 (4096 + (1472 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block24 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1536 + m.val)) = forwardAction (forwardTable0 (4096 + (1536 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block25 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1600 + m.val)) = forwardAction (forwardTable0 (4096 + (1600 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block26 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1664 + m.val)) = forwardAction (forwardTable0 (4096 + (1664 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block27 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1728 + m.val)) = forwardAction (forwardTable0 (4096 + (1728 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block28 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1792 + m.val)) = forwardAction (forwardTable0 (4096 + (1792 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block29 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1856 + m.val)) = forwardAction (forwardTable0 (4096 + (1856 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block30 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1920 + m.val)) = forwardAction (forwardTable0 (4096 + (1920 + m.val))) 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem forward_checked1_part2_block31 : ∀ m : Fin 64,
    forwardTable1 (4096 + (1984 + m.val)) = forwardAction (forwardTable0 (4096 + (1984 + m.val))) 1 := by
  decide +kernel

theorem forward_checked1_part2 (m : Fin 2048) :
    forwardTable1 (4096 + m.val) = forwardAction (forwardTable0 (4096 + m.val)) 1 := by
  apply check_blocks (P := fun a => forwardTable1 (4096 + a) = forwardAction (forwardTable0 (4096 + a)) 1)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact forward_checked1_part2_block0
  · exact forward_checked1_part2_block1
  · exact forward_checked1_part2_block2
  · exact forward_checked1_part2_block3
  · exact forward_checked1_part2_block4
  · exact forward_checked1_part2_block5
  · exact forward_checked1_part2_block6
  · exact forward_checked1_part2_block7
  · exact forward_checked1_part2_block8
  · exact forward_checked1_part2_block9
  · exact forward_checked1_part2_block10
  · exact forward_checked1_part2_block11
  · exact forward_checked1_part2_block12
  · exact forward_checked1_part2_block13
  · exact forward_checked1_part2_block14
  · exact forward_checked1_part2_block15
  · exact forward_checked1_part2_block16
  · exact forward_checked1_part2_block17
  · exact forward_checked1_part2_block18
  · exact forward_checked1_part2_block19
  · exact forward_checked1_part2_block20
  · exact forward_checked1_part2_block21
  · exact forward_checked1_part2_block22
  · exact forward_checked1_part2_block23
  · exact forward_checked1_part2_block24
  · exact forward_checked1_part2_block25
  · exact forward_checked1_part2_block26
  · exact forward_checked1_part2_block27
  · exact forward_checked1_part2_block28
  · exact forward_checked1_part2_block29
  · exact forward_checked1_part2_block30
  · exact forward_checked1_part2_block31


end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
