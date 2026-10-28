module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.FiniteSource
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.Source

/-!
# Unconditional Ree involution bounds on the model and its quasisimple covers

The universal semisimple-center theorem and the actual odd-order class bound
now discharge the last two source inputs of the finite tensor construction.
The resulting involution estimates apply to the original module and literal
central quotient, without a representation, class-count or geometry premise.
Source: Guralnick--Malle II, Lemma 8.8; Steinberg (1963), 3.9 and 12.2.
-/

public section
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate
universe u v

/-- The intrinsic binary involution estimate for every source Ree parameter. -/
theorem binaryModelInvolutionBound_source {m : ℕ} (hm : 1 ≤ m) :
    BinaryModelInvolutionBound.{v} m :=
  binaryModelInvolutionBound_of_class_bound_and_semisimple_centers
    (fun _ _ _ _ _ _ hH _ hT =>
      SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)
    (Classification.Steinberg.Geometry.OddClasses.model_odd_class_bound m) hm

/-- The same estimate on an arbitrary original quasisimple central cover. -/
theorem coverInvolutionBound_source {m : ℕ} (hm : 1 ≤ m) :
    CoverInvolutionBound.{u,v} m :=
  coverInvolutionBound_of_binary_source hm (binaryModelInvolutionBound_source hm)

end ReeF4.FixedSpaceEstimate
