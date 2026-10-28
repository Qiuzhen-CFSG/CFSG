module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates.FixedScalars
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.RootCoordinates.GraphField

/-!
# Actual finite-cell coordinates from the proved root parameter laws

Unique ordered root coordinates intertwine graph-field action with the scalar
twist. The fixed positive and negative radicals lie in the literal elementary
subgroup. Combining these facts with finite-field descent gives both exact
coordinate equivalences and their ambient root-product equations.
No whole-fixed-group generation assumption is used.
Source: Steinberg 6.2(b), 11.8 and 13.3(a).
-/

public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup CyclicDimension ClassBound
open CoordinateScalars
universe u
variable {k:Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K:Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem ordered_mem (S:Geometry K) (Q:Set S.roots.Root) (r:Fin 12→S.roots.Root)
    (hr:∀i,r i∈Q) (x:Fin 12→k) :
    orderedRootPoint S r x∈RootSubgroupGenerated S.roots Q := by
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz
  exact rootSubgroup_le_RootSubgroupGenerated S.roots (hr i)
    ((S.roots.rootSubgroup (r i)).pointEquiv _).property

private def cellOfFixedTuple (S:Geometry K) (n:ℕ) (Q:Set S.roots.Root)
    (r:Fin 12→S.roots.Root) (hr:∀i,r i∈Q)
    (htwist:∀x,graphFieldEnd S n (orderedRootPoint S r x)=
      orderedRootPoint S r (parameterTwist n x))
    (hkeep:(RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (x:{x:Fin 12→k //parameterTwist n x=x}) : finiteCell S n Q := by
  let g:graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n :=
    ⟨orderedRootPoint S r x.val,by
      change graphFieldEnd S n (orderedRootPoint S r x.val)=orderedRootPoint S r x.val
      rw [htwist,x.property]⟩
  have hg:g∈(RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype :=
    ordered_mem S Q r hr x.val
  exact ⟨⟨g,hkeep hg⟩,hg⟩

omit [IsAlgClosed k] in
private theorem cellOfFixedTuple_bijective (S:Geometry K) (n:ℕ) (Q:Set S.roots.Root)
    (r:Fin 12→S.roots.Root) (hr:∀i,r i∈Q)
    (htwist:∀x,graphFieldEnd S n (orderedRootPoint S r x)=
      orderedRootPoint S r (parameterTwist n x))
    (hkeep:(RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hinj:Function.Injective (orderedRootPoint S r))
    (hsur:∀g∈RootSubgroupGenerated S.roots Q,∃x,orderedRootPoint S r x=g) :
    Function.Bijective (cellOfFixedTuple S n Q r hr htwist hkeep) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply hinj
    exact congrArg (cellInclusion S n Q) he
  · intro g
    obtain ⟨x,hx⟩:=hsur (cellInclusion S n Q g) (cellInclusion_mem S n Q g)
    have ht:parameterTwist n x=x := by
      apply hinj
      rw [←htwist,hx]
      exact g.val.val.property
    refine ⟨⟨x,ht⟩,?_⟩
    apply cellInclusion_injective S n Q
    exact hx

private def cellEquivFixedTuples (S:Geometry K) (n:ℕ) (Q:Set S.roots.Root)
    (r:Fin 12→S.roots.Root) (hr:∀i,r i∈Q)
    (htwist:∀x,graphFieldEnd S n (orderedRootPoint S r x)=
      orderedRootPoint S r (parameterTwist n x))
    (hkeep:(RootSubgroupGenerated S.roots Q).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hinj:Function.Injective (orderedRootPoint S r))
    (hsur:∀g∈RootSubgroupGenerated S.roots Q,∃x,orderedRootPoint S r x=g) :
    {x:Fin 12→k //parameterTwist n x=x} ≃ finiteCell S n Q :=
  Equiv.ofBijective (cellOfFixedTuple S n Q r hr htwist hkeep)
    (cellOfFixedTuple_bijective S n Q r hr htwist hkeep hinj hsur)

def twistedCellCoordinates_of_relations (S:Geometry K) (hrel:RootPairParameterRelations S)
    (n:ℕ) (hn:0<n) (f:Triality.Standard.ExtensionField
      (Triality.Standard.binaryParameters n hn)→+*k) :
    TwistedCellCoordinates S n (Triality.Standard.binaryParameters n hn) := by
  have hpos:∀i,positiveCoordinateRoot S i∈S.roots.positive := by
    intro i
    apply (S.positive _).mpr
    simpa only [positiveCoordinateRoot,Equiv.apply_symm_apply] using
      Triality.Standard.PositiveCoordinates.rootIndex_positive i
  have hneg:∀i,negativeCoordinateRoot S i∈S.roots.neg ⁻¹' S.roots.positive := by
    intro i
    change S.roots.neg (S.roots.neg (positiveCoordinateRoot S i))∈S.roots.positive
    rw [S.realized.neg_neg]
    exact hpos i
  refine {
    coefficientEmbedding:=f
    positive:=(CoordinateScalars.fixedCoordinatesEquiv f).trans
      (cellEquivFixedTuples S n _ _ hpos (positive_ordered_graphField S hrel n)
        (positiveFixed_le_elementary S n) (positive_root_coordinates S hrel).1
        (positive_root_coordinates S hrel).2)
    negative:=(CoordinateScalars.fixedCoordinatesEquiv f).trans
      (cellEquivFixedTuples S n _ _ hneg (negative_ordered_graphField S hrel n)
        (negativeFixed_le_elementary S n) (negative_root_coordinates S hrel).1
        (negative_root_coordinates S hrel).2)
    positive_point:=fun a=>rfl
    negative_point:=fun a=>rfl}
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
