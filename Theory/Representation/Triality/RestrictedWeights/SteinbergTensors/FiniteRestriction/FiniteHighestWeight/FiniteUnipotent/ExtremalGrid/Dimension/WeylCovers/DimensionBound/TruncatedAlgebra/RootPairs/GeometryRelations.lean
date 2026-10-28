module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.GeometryRelations.Nonvanishing

/-!
# D4 root-pair parameter relations from positive laws and rank-one charts

The positive-system input permits zero exchange constants. Actual simultaneous
Weyl transport extends its laws to all distinct nonopposite roots, retaining
the nonzero rescalings of the arbitrarily chosen root parameters. The rank-one
word contradiction then excludes zero constants for every root sum.

The theorem below is conditional precisely on the three displayed geometric
inputs. Their construction remains with the corresponding assembly owners.
It assumes no Chevalley system or comparison with a concrete group model.

Sources: GLS3 1.12.1(b,h), 1.12.7; Chapter2St2 6.2(b);
Steinberg, Representations of algebraic groups (1963), §2.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open ClassBound ClassBound.FixedOpposition.AmbientNormalizer
open CorootRealization RootPairGeometry
public noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Positive root laws, actual root-subgroup uniqueness and the four SL₂ charts
imply the full parameter relations, with nonzero exchange constants. -/
theorem rootPairParameterRelations_of_positive_and_charts (S : Geometry K)
    (hcharts : ∀ i : Fin 4, Nonempty (SimpleRootSL2Chart S i))
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (hpos : PositiveRootPairParameterRelations S) : RootPairParameterRelations S := by
  let D := simpleCorootWordData_of_charts S (fun i => Classical.choice (hcharts i))
  refine ⟨all_commute_of_positive S hu D hpos, ?_⟩
  intro a b c hs
  obtain ⟨κ, hk⟩ := all_exchange_of_positive S hu D hpos a b c hs
  refine ⟨κ, ?_, hk⟩
  intro hκ
  subst κ
  exact rootSum_not_commute S hu D hpos a b c hs (pairExchange_zero_commutes S a b c hk)

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
