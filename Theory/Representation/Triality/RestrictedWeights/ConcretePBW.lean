module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRelations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.SourcePBW

/-!
# Concrete triality cyclic dimension bounds from the proved PBW span

The pinned root relations and actual simple SL2 charts discharge the source
PBW hypotheses. The proved normalization and highest-vector orbit producer
identify the full coefficient-algebra orbit with the original cyclic module.
Counting its ordered root-coefficient tuples now gives the required q^12
bound, for both Borel conventions and including q=2.

Only the independently owned universality of the actual Spin group remains
as a geometric input. This is the literal finite-module consumer needed by
the triality inner-displacement argument, without an additional module table.
Source: Steinberg (1963), sections 2–3 and 13.2(d).
-/

open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
open ExtremalGrid ExtremalGrid.CyclicDimension
namespace Triality.RestrictedWeights.Concrete
@[expose] public noncomputable section
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))
theorem cyclicHighest_dimensionBound (n:ℕ) :
    CyclicHighestWeightDimensionBound (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.B
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n)) ((2^n)^12) := by
  intro C
  have htri := SourcePBW.positive_triangular_spanning (finiteGeometry k hu)
    (rootPairParameterRelations k hu) (RankOne.simpleCharts k hu) C.action C.rational n C.highest
  have htop := cyclicHighest_operatorOrbit_eq_top k hu n C
  have hs : orderedCoefficientSpan (finiteGeometry k hu) C.action C.rational
      (negativeCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector=⊤ :=
    top_unique (htop ▸ htri)
  calc
    Module.finrank k C.Space = Module.finrank k (⊤ : Submodule k C.Space) := (finrank_top k C.Space).symm
    _ = Module.finrank k (orderedCoefficientSpan (finiteGeometry k hu) C.action C.rational
        (negativeCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector) :=
      congrArg (fun U : Submodule k C.Space => Module.finrank k U) hs.symm
    _ ≤ (2^n)^12 := finrank_orderedCoefficientSpan_le (finiteGeometry k hu)
      C.action C.rational (negativeCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector

theorem cyclicOppositeHighest_dimensionBound (n:ℕ) :
    CyclicHighestWeightDimensionBound (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.Bopp
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))⁻¹ ((2^n)^12) := by
  intro C
  have htri := SourcePBW.opposite_triangular_spanning (finiteGeometry k hu)
    (rootPairParameterRelations k hu) (RankOne.simpleCharts k hu) C.action C.rational n C.highest
  have htop := cyclicOppositeHighest_operatorOrbit_eq_top k hu n C
  have hs : orderedCoefficientSpan (finiteGeometry k hu) C.action C.rational
      (positiveCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector=⊤ :=
    top_unique (htop ▸ htri)
  calc
    Module.finrank k C.Space = Module.finrank k (⊤ : Submodule k C.Space) := (finrank_top k C.Space).symm
    _ = Module.finrank k (orderedCoefficientSpan (finiteGeometry k hu) C.action C.rational
        (positiveCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector) :=
      congrArg (fun U : Submodule k C.Space => Module.finrank k U) hs.symm
    _ ≤ (2^n)^12 := finrank_orderedCoefficientSpan_le (finiteGeometry k hu)
      C.action C.rational (positiveCoordinateRoot (finiteGeometry k hu)) (2^n) C.vector
end
end Triality.RestrictedWeights.Concrete
