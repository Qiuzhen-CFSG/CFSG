module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteGeometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RankOneSource
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.SimpleRootOrbits
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.Transport

/-!
# Concrete rank-one charts and the finite triality coefficient bound

The actual regular SL₂ maps give the four compatible opposite-root charts.
Their source-convention diagonals lie in the prescribed coroot torus. Applying
the rank-one degree calculation bounds the simple-root orbits of every cyclic
extremal highest-weight vector by the actual truncated coefficient algebra,
for both Borel signs. This discharges the rank-one orbit premise of the finite
restriction interpolation argument; normalization and triangular spanning
remain separate earlier inputs.
Source: GLS3 §§1.9–1.12; Steinberg 6.1 and 13.2(d).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
namespace Triality.SimplyConnected.Pinning.RankOne
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
open Triality.RestrictedWeights.Concrete

theorem simpleCharts (hu : IsUniversalVersion (groupVariety k)) (i : Fin 4) :
    Nonempty (SimpleRootSL2Chart (finiteGeometry k hu) i) := by
  obtain ⟨f,hp,hm⟩ := hasRootMap_simple k i
  let X := (pinnedRootData k).rootSubgroup (pinnedRootIndex k (simpleRoot i))
  let Y := (pinnedRootData k).rootSubgroup ((pinnedRootData k).neg (pinnedRootIndex k (simpleRoot i)))
  let := X.carrierAlgebraicGroup
  let := Y.carrierAlgebraicGroup
  refine ⟨BinaryOppositeRootSL2Chart.ofAmbient (CorootTorus.closedSubgroup k) X Y
    (pinnedRootParametrization k _) (pinnedRootParametrization k _) f ?_ ?_ ?_⟩
  · apply Morphism.ext
    funext s
    obtain ⟨a,rfl⟩ := (additiveGroupPointEquiv k).symm.surjective s
    exact (hp a.toAdd).trans (pinnedRootParametrization_inclusion k _ a.toAdd).symm
  · apply Morphism.ext
    funext s
    obtain ⟨a,rfl⟩ := (additiveGroupPointEquiv k).symm.surjective s
    change f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint a.toAdd)) = _
    rw [hm]
    change rootPoint k (negativeRoot (simpleRoot i)) a.toAdd =
      ((pinnedRootData k).rootSubgroup ((pinnedRootData k).neg (pinnedRootIndex k (simpleRoot i)))).includePoint
        ((pinnedRootParametrization k _).value a.toAdd)
    rw [pinnedRootParametrization_inclusion, pinnedRootData_neg]
    rfl

  · intro t
    rw [rootMap_coroot k f hp hm]
    change corootWord k (pinnedRootIndex k (simpleRoot i)).down _ ∈ _
    rw [← pinnedRootData_rootCocharacter k (pinnedRootIndex k (simpleRoot i)) t]
    exact ((CorootTorus.closedSubgroup k).pointEquiv _).property


open ExtremalGrid ExtremalGrid.CyclicDimension
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem cyclicHighest_simpleRootAction_mem_source
    (hu : IsUniversalVersion (groupVariety k)) (n : ℕ)
    (C : CyclicHighestWeightModule (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.B
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n)))
    (g : (groupVariety k).Point) (hg : g ∈ simpleRootPoints (finiteGeometry k hu)) :
    (C.action.action g).val C.vector ∈
      operatorOrbit (coefficientAlgebra (finiteGeometry k hu) C.action C.rational (2^n)) C.vector :=
  cyclicHighest_simpleRootAction_mem (finiteGeometry k hu) (simpleCharts k hu) n C g hg

theorem cyclicOppositeHighest_simpleRootAction_mem_source
    (hu : IsUniversalVersion (groupVariety k)) (n : ℕ)
    (C : CyclicHighestWeightModule (finiteGeometry k hu) (finiteGeometry k hu).bigCell.data.Bopp
      ((finiteGeometry k hu).leftWeightEmbedding (maximalRestrictedWeight n))⁻¹)
    (g : (groupVariety k).Point) (hg : g ∈ simpleRootPoints (finiteGeometry k hu)) :
    (C.action.action g).val C.vector ∈
      operatorOrbit (coefficientAlgebra (finiteGeometry k hu) C.action C.rational (2^n)) C.vector :=
  cyclicOppositeHighest_simpleRootAction_mem (finiteGeometry k hu) (simpleCharts k hu) n C g hg

end Triality.SimplyConnected.Pinning.RankOne
