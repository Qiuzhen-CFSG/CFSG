module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 8

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
    row (0 + m.val + 256) = fastRow (row (0 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_1 : ∀ m : Fin 64,
    row (64 + m.val + 256) = fastRow (row (64 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_2 : ∀ m : Fin 64,
    row (128 + m.val + 256) = fastRow (row (128 + m.val)) 8 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_3 : ∀ m : Fin 64,
    row (192 + m.val + 256) = fastRow (row (192 + m.val)) 8 := by
  decide +kernel

theorem row_step_8 (m : Fin 256) :
    row (m.val + 256) = packedRow (row m.val) (factorRows 8) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 256) = fastRow (row k) 8)
    (size := 64) (blocks := 4) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
