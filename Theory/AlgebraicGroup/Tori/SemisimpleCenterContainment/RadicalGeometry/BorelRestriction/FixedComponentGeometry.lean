module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.InvariantAction
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.ConnectedPreimage
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry.OrbitOpenness

/-!
# Fixed-component geometry for Borel restriction

The connected centralizer acts regularly on the published reduced fixed component,
and its inclusion is equivariant for the actual ambient action. For a connected
ambient group, the reduced inverse image of each fixed component under the actual
orbit morphism is connected. The orbit morphism is an open surjection on scheme
points, and its closed fibres are connected because the stabilizer is a Borel.
This argument permits inseparable orbit morphisms.

These are the component-invariance and inverse-image connectedness steps of
Borel, *Linear Algebraic Groups*, §11.15. Centralizer transitivity is left to the
Borel restriction assembly (`refs/KGroup/Bor1/Chapter4.tex`).
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

/-- Apply the open-map connectedness argument to the actual irreducible component.
No basepoint-membership premise is needed for this geometric step. -/
public theorem fixedComponentPreimage_isConnected_of_isOpenMap
    {B : ClosedSubgroup H} (M : CompleteModel B) (hB : IsBorelSubgroup B)
    (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (hπ : IsOpenMap (M.action.orbitMorphismAt (modelBasePoint M)).hom) :
    Variety.Geometric.IsConnected (componentPreimage M (fixedComponent M S Z)).toGeometric := by
  let : IrreducibleSpace (fixedComponent M S Z).toGeometric.toScheme :=
    fixedComponent_isIrreducible M S Z
  apply componentPreimage_isConnected_of_isOpenMap M hB (fixedComponent M S Z) _ hπ
  change ConnectedSpace (fixedComponent M S Z).toGeometric.toScheme
  infer_instance

/-- Over a connected ambient group, the reduced inverse image of every actual
fixed component under the Borel-model orbit morphism is connected. This applies
in particular to the component containing the Borel basepoint in §11.15; neither
basepoint membership nor the subtorus condition is needed for this step. -/
public theorem fixedComponentPreimage_isConnected
    {B : ClosedSubgroup H} (M : CompleteModel B) (hH : Variety.IsConnected H)
    (hB : IsBorelSubgroup B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    Variety.Geometric.IsConnected (componentPreimage M (fixedComponent M S Z)).toGeometric :=
  fixedComponentPreimage_isConnected_of_isOpenMap M hB S Z (modelOrbit_isOpenMap M hH)

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
