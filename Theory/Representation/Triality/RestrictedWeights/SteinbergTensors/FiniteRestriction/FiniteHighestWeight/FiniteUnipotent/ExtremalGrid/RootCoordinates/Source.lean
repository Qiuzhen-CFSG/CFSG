module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.CommutatorContainment
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Separation
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Product
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.DenseParameters.OppositeGeometry
/-!
# Unique actual root coordinates from source parameter relations

The sum-root exchange law gives relative normalization of each tail of the
fixed twelve-root order. Character separation already proves the required
trivial intersections. Their group-theoretic factorization yields existence
and uniqueness in that literal order. Apply the same argument to opposite
root data for the negative cell, preserving every root parameter.
Source: GLS3 1.12.7 and Steinberg 6.2(b).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open CyclicDimension ClassBound.ConnectedCentralizer.Bruhat
universe u
variable {k:Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K:Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem product_eq (S:Geometry K) (x:Fin 12→k) :
    toralOrderedRootProduct S.roots S.rootParameter (Coordinates.positiveOrder S)
      (fun i=>x ⟨i.val,by simpa only [Coordinates.positiveOrder_length] using i.isLt⟩) =
    orderedRootPoint S (positiveCoordinateRoot S) x := by
  unfold toralOrderedRootProduct Coordinates.positiveOrder orderedRootPoint
  rfl

/-- Unique actual coordinates in the specified positive root order. -/
theorem positive_root_coordinates (S:Geometry K) (hrel:RootPairParameterRelations S) :
    Function.Injective (orderedRootPoint S (positiveCoordinateRoot S)) ∧
    ∀ g∈RootSubgroupGenerated S.roots S.roots.positive,
      ∃ x,orderedRootPoint S (positiveCoordinateRoot S) x=g := by
  obtain ⟨hi,hs⟩ := toralOrderedRootProduct_unique_and_covers_of_suffixes
    S.roots S.rootParameter (Coordinates.positiveOrder S)
    (tailNormalizes_of_positiveCommutatorContainment S
      (positiveCommutatorContainment_of_relations S hrel)) (positive_tailDisjoint S)
  constructor
  · intro x y h
    have he := hi ((product_eq S x).trans (h.trans (product_eq S y).symm))
    funext i
    exact congrFun he ⟨i.val,by simpa only [Coordinates.positiveOrder_length] using i.isLt⟩
  · intro g hg
    have hset : {a | a∈Coordinates.positiveOrder S}=S.roots.positive :=
      Set.ext (Coordinates.mem_positiveOrder S)
    rw [hset] at hs
    obtain ⟨x,hx⟩ := hs g hg
    refine ⟨fun i=>x ⟨i.val,by simpa only [Coordinates.positiveOrder_length] using i.isLt⟩,?_⟩
    rw [← product_eq]
    exact hx

omit [IsAlgClosed k] in
private theorem rootSum_neg_iff (S:Geometry K) (a b c:S.roots.Root) :
    RootSum S (S.roots.neg a) (S.roots.neg b) (S.roots.neg c) ↔ RootSum S a b c := by
  simp only [RootSum,S.based.2.2.1,RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self,← neg_add,neg_inj]

/-- Negating every actual root preserves the parameter relations. -/
theorem rootPairParameterRelations_opposite (S:Geometry K) (hrel:RootPairParameterRelations S) :
    RootPairParameterRelations S.opposite := by
  constructor
  · intro a b hab hneg hsum s t
    change Commute ((rootCurve S (S.roots.neg a)).onPoints (kPlusPoint s))
      ((rootCurve S (S.roots.neg b)).onPoints (kPlusPoint t))
    apply hrel.commute _ _
    · exact fun h => hab ((Function.Involutive.injective S.realized.neg_neg) h)
    · intro h
      apply hneg
      exact (Function.Involutive.injective S.realized.neg_neg) h
    · rintro ⟨c,hc⟩
      apply hsum
      refine ⟨S.roots.neg c,?_⟩
      change RootSum S a b (S.roots.neg c)
      apply (rootSum_neg_iff S a b (S.roots.neg c)).mp
      simpa only [S.realized.neg_neg] using hc
  · intro a b c hc
    exact hrel.exchange _ _ _ ((rootSum_neg_iff S a b c).mpr hc)

/-- The opposite coordinate map uses the negatives of exactly the same roots. -/
theorem negative_root_coordinates (S:Geometry K) (hrel:RootPairParameterRelations S) :
    Function.Injective (orderedRootPoint S (negativeCoordinateRoot S)) ∧
    ∀ g∈RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive),
      ∃ x,orderedRootPoint S (negativeCoordinateRoot S) x=g := by
  have h := positive_root_coordinates S.opposite (rootPairParameterRelations_opposite S hrel)
  rw [S.opposite_positive_generated] at h
  exact h
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
