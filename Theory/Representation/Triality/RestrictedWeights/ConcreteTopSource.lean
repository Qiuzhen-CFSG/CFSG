module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootUniqueness
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRelations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.Source

/-!
# Actual Spin extremal divided-power endpoints

The pinned charts, root relations and proved tangent span discharge every
geometric input of the twelve-step top-word argument. The chart opposition
word gives an actual ambient inverter, so both cyclic highest-weight modules
have the required nonzero scalar endpoint with no extra operator premise.
These are the coefficient facts needed by finite-cell interpolation; finite
highest-weight realization remains the consuming assembly.
Source: Steinberg (1963), sections 2.8 and 4.3; GLS3 13.2(d).
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
open ExtremalGrid ExtremalGrid.CyclicDimension ExtremalGrid.DividedPowerEndpoint
open ClassBound.FixedOpposition.AmbientNormalizer
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
namespace Triality.RestrictedWeights.Concrete
universe u v
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

/-- The actual chart opposition word inverts the whole prescribed torus. -/
theorem exists_torus_inverter : ∃ r : (groupVariety k).Point,
    ∀ t : (finiteGeometry k hu).torus.carrierVariety.Point,
      r*(finiteGeometry k hu).torus.includePoint t*r⁻¹ =
        ((finiteGeometry k hu).torus.includePoint t)⁻¹ := by
  let C := fun i => Classical.choice (RankOne.simpleCharts k hu i)
  let D := (simpleCorootWordData_of_charts (finiteGeometry k hu) C).toSimpleReflectionLifts
  exact ⟨D.oppositionRepresentative, fun t => D.oppositionRepresentative_inverts _
    (((finiteGeometry k hu).torus.pointEquiv t).property)⟩

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Nonvanishing for the literal negative height-ordered word on the source module. -/
theorem negative_topOperator_ne_zero (rho : RationalRepresentation (groupVariety k) V)
    (hr : IsRationalRepresentation rho) (n : ℕ) (v : V)
    (hv : HasHighWeight rho (finiteGeometry k hu).bigCell.data.B
      (finiteGeometry k hu).torus v
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))) :
    topOperator (finiteGeometry k hu) rho hr
      (negativeCoordinateRoot (finiteGeometry k hu)) n v ≠ 0 :=
  DividedPowerEndpoint.negative_topOperator_ne_zero (finiteGeometry k hu)
    (RankOne.simpleCharts k hu) (rootSubgroupUniqueness k hu)
    (rootPairParameterRelations k hu) rho hr n v hv

/-- Nonvanishing for the literal positive word on an opposite highest vector. -/
theorem positive_topOperator_ne_zero (rho : RationalRepresentation (groupVariety k) V)
    (hr : IsRationalRepresentation rho) (n : ℕ) (v : V)
    (hv : HasHighWeight rho (finiteGeometry k hu).bigCell.data.Bopp
      (finiteGeometry k hu).torus v
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))⁻¹) :
    topOperator (finiteGeometry k hu) rho hr
      (positiveCoordinateRoot (finiteGeometry k hu)) n v ≠ 0 :=
  DividedPowerEndpoint.positive_topOperator_ne_zero (finiteGeometry k hu)
    (RankOne.simpleCharts k hu) (rootSubgroupUniqueness k hu)
    (rootPairParameterRelations k hu) rho hr n v hv

/-- The full actual endpoint, including construction of its torus inverter. -/
theorem negative_extremal_endpoint (rho : RationalRepresentation (groupVariety k) V)
    (hr : IsRationalRepresentation rho) (n : ℕ) (v : V)
    (hv : HasHighWeight rho (finiteGeometry k hu).bigCell.data.B
      (finiteGeometry k hu).torus v
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n)))
    (hcyc : IsCyclicRepresentation rho v) :
    ∃ (r : (groupVariety k).Point) (c:k), c≠0 ∧
      (∀ t : (finiteGeometry k hu).torus.carrierVariety.Point,
        r*(finiteGeometry k hu).torus.includePoint t*r⁻¹ =
          ((finiteGeometry k hu).torus.includePoint t)⁻¹) ∧
      topOperator (finiteGeometry k hu) rho hr
        (negativeCoordinateRoot (finiteGeometry k hu)) n v = c • (rho.action r).val v := by
  obtain ⟨r,hi⟩ := exists_torus_inverter k hu
  obtain ⟨c,hc,he⟩ := negative_endpoint_of_source (finiteGeometry k hu)
    (RankOne.simpleCharts k hu) (rootSubgroupUniqueness k hu)
    (rootPairParameterRelations k hu) rho hr n v hv hcyc r hi
  exact ⟨r,c,hc,hi,he⟩

/-- The full opposite endpoint uses the same genuine pinned geometry. -/
theorem positive_extremal_endpoint (rho : RationalRepresentation (groupVariety k) V)
    (hr : IsRationalRepresentation rho) (n : ℕ) (v : V)
    (hv : HasHighWeight rho (finiteGeometry k hu).bigCell.data.Bopp
      (finiteGeometry k hu).torus v
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (hcyc : IsCyclicRepresentation rho v) :
    ∃ (r : (groupVariety k).Point) (c:k), c≠0 ∧
      (∀ t : (finiteGeometry k hu).torus.carrierVariety.Point,
        r*(finiteGeometry k hu).torus.includePoint t*r⁻¹ =
          ((finiteGeometry k hu).torus.includePoint t)⁻¹) ∧
      topOperator (finiteGeometry k hu) rho hr
        (positiveCoordinateRoot (finiteGeometry k hu)) n v = c • (rho.action r).val v := by
  obtain ⟨r,hi⟩ := exists_torus_inverter k hu
  obtain ⟨c,hc,he⟩ := positive_endpoint_of_source (finiteGeometry k hu)
    (RankOne.simpleCharts k hu) (rootSubgroupUniqueness k hu)
    (rootPairParameterRelations k hu) rho hr n v hv hcyc r hi
  exact ⟨r,c,hc,hi,he⟩

end Triality.RestrictedWeights.Concrete
