module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 7

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
    row (0 + m.val + 128) = fastRow (row (0 + m.val)) 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem step_1 : ∀ m : Fin 64,
    row (64 + m.val + 128) = fastRow (row (64 + m.val)) 7 := by
  decide +kernel

theorem row_step_7 (m : Fin 128) :
    row (m.val + 128) = packedRow (row m.val) (factorRows 7) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 128) = fastRow (row k) 7)
    (size := 64) (blocks := 2) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0
  · exact step_1

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
