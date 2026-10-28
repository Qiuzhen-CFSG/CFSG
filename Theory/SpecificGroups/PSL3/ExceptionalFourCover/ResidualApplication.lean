module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Recognition
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels

/-!
# Applying the exceptional kernel calculation to the fixed residuals

The proved exceptional multiplier discharges the literal
`UniversalKernelInvolutionsAreSquares` premise of the existing graph and
field residual projections. The graph's projective model remains its
separate geometric premise; the field model is already proved. The earlier
conditional interfaces are retained as well.

This is the use of I.1.3(6) in Aschbacher–Smith 15.3.38, printed
pp.1136–1137.
-/

public section

open Theory.GroupTheory
open Subgroup

namespace Matrix.PSL3.ExceptionalFourCover

variable {L : Type} [Group L] [Finite L] [IsQuasisimple L]

/-- The two multiplier calculations supply exactly the square-root premise of the consumer. -/
theorem universalKernelInvolutionsAreSquares_of_cover_and_bound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    PSL3Four.UniversalKernelInvolutionsAreSquares :=
  PSL3Four.universalKernelInvolutionsAreSquares_of_model
    (canonicalKernelEquivOfCoverAndBound f e hbound)

/-- The exceptional multiplier supplies square roots for all universal-kernel involutions. -/
theorem universalKernelInvolutionsAreSquares :
    PSL3Four.UniversalKernelInvolutionsAreSquares :=
  PSL3Four.universalKernelInvolutionsAreSquares_of_model canonicalKernelEquiv

variable {E : Type*} [Group E] [Finite E] {c : PSL3Four.FourCover E}

/-- The actual field residual projection, with its exceptional multiplier premise discharged. -/
theorem fieldResidualProjection_injective_of_cover_and_bound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) (a : PSL3Four.CoverActions E c) :
    Function.Injective a.fieldResidualProjection :=
  a.fieldResidualProjection_injective_of_kernel_squares
    (universalKernelInvolutionsAreSquares_of_cover_and_bound f e hbound)

/-- The actual graph residual projection, retaining only its independent projective model. -/
theorem graphResidualProjection_injective_of_cover_and_bound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) (a : PSL3Four.CoverActions E c)
    (d : pResidual 2 (PSL3.OuterSolvable.graph PSL3Four.F).fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) PSL3Four.F) :
    Function.Injective a.graphResidualProjection :=
  a.graphResidualProjection_injective_of_kernel_squares
    (universalKernelInvolutionsAreSquares_of_cover_and_bound f e hbound) d

/-- The actual field residual projection is injective, with the multiplier input proved. -/
theorem fieldResidualProjection_injective (a : PSL3Four.CoverActions E c) :
    Function.Injective a.fieldResidualProjection :=
  a.fieldResidualProjection_injective_of_kernel_squares
    universalKernelInvolutionsAreSquares

/-- Graph injectivity with only the independent projective-model premise remaining. -/
theorem graphResidualProjection_injective_of_projective_model
    (a : PSL3Four.CoverActions E c)
    (d : pResidual 2 (PSL3.OuterSolvable.graph PSL3Four.F).fixedSubgroup ≃*
      ProjectiveSpecialLinearGroup (Fin 2) PSL3Four.F) :
    Function.Injective a.graphResidualProjection :=
  a.graphResidualProjection_injective_of_kernel_squares
    universalKernelInvolutionsAreSquares d

end Matrix.PSL3.ExceptionalFourCover
