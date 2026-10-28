module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks

/-!
# First-row updates for factor 0

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
private theorem step_0 : ∀ m : Fin 1,
    row (0 + m.val + 1) = fastRow (row (0 + m.val)) 0 := by
  decide +kernel

theorem row_step_0 (m : Fin 1) :
    row (m.val + 1) = packedRow (row m.val) (factorRows 0) := by
  rw [← fastRow_eq]
  apply check_blocks (P := fun k => row (k + 1) = fastRow (row k) 0)
    (size := 1) (blocks := 1) (by decide) ?_ m
  intro b
  fin_cases b
  · exact step_0

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
