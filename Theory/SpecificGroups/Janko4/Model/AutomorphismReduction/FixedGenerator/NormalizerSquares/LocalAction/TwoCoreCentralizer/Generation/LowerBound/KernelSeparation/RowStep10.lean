module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 10

The update appends the highest selected factor on the right.
These are equalities of packed rows, checked in the kernel.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
private theorem step_0 : ∀ m : Fin 64,
    row (0 + m.val + 1024) = fastRow (row (0 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_1 : ∀ m : Fin 64,
    row (64 + m.val + 1024) = fastRow (row (64 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_2 : ∀ m : Fin 64,
    row (128 + m.val + 1024) = fastRow (row (128 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_3 : ∀ m : Fin 64,
    row (192 + m.val + 1024) = fastRow (row (192 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_4 : ∀ m : Fin 64,
    row (256 + m.val + 1024) = fastRow (row (256 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_5 : ∀ m : Fin 64,
    row (320 + m.val + 1024) = fastRow (row (320 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_6 : ∀ m : Fin 64,
    row (384 + m.val + 1024) = fastRow (row (384 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_7 : ∀ m : Fin 64,
    row (448 + m.val + 1024) = fastRow (row (448 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_8 : ∀ m : Fin 64,
    row (512 + m.val + 1024) = fastRow (row (512 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_9 : ∀ m : Fin 64,
    row (576 + m.val + 1024) = fastRow (row (576 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_10 : ∀ m : Fin 64,
    row (640 + m.val + 1024) = fastRow (row (640 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_11 : ∀ m : Fin 64,
    row (704 + m.val + 1024) = fastRow (row (704 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_12 : ∀ m : Fin 64,
    row (768 + m.val + 1024) = fastRow (row (768 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_13 : ∀ m : Fin 64,
    row (832 + m.val + 1024) = fastRow (row (832 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_14 : ∀ m : Fin 64,
    row (896 + m.val + 1024) = fastRow (row (896 + m.val)) 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_15 : ∀ m : Fin 64,
    row (960 + m.val + 1024) = fastRow (row (960 + m.val)) 10 := by
  decide +kernel

theorem row_step_10 (m : Fin 1024) :
    row (m.val + 1024) = packedRow (row m.val) (factorRows 10) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 1024) = fastRow (row k) 10)
    (size := 64) (blocks := 16) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
