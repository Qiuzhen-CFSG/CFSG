module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 6

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
    row (0 + m.val + 64) = fastRow (row (0 + m.val)) 6 := by
  decide +kernel

theorem row_step_6 (m : Fin 64) :
    row (m.val + 64) = packedRow (row m.val) (factorRows 6) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 64) = fastRow (row k) 6)
    (size := 64) (blocks := 1) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
