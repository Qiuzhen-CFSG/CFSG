module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 4

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
private theorem step_0 : ∀ m : Fin 16,
    row (0 + m.val + 16) = fastRow (row (0 + m.val)) 4 := by
  decide +kernel

theorem row_step_4 (m : Fin 16) :
    row (m.val + 16) = packedRow (row m.val) (factorRows 4) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 16) = fastRow (row k) 4)
    (size := 16) (blocks := 1) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
