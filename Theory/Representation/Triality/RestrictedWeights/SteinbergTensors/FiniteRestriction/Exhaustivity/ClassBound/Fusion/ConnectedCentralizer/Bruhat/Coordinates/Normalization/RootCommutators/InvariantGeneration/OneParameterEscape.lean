module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.ClosedRoots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.OneParameterEscape.Dimension

/-!
# One-parameter escape from the canonical contained-root subgroup

The proved reduction constructs an escaping subtorus fixed subgroup of `X`.
It is connected, unipotent, invariant under the full torus, and has positive
dimension. A bound of one for these fixed subgroups makes its dimension exactly
one. The classification of connected one-dimensional unipotent groups then
supplies an actual additive-group parametrization of this ambient subgroup.

`OneParameterEscape.Dimension` reduces the dimension bound to earlier
Borel geometry. That geometry and the one-dimensional classification remain
explicit prerequisites. The unconditional `invariantOneParameterEscape` is
not asserted here until those prerequisites have been discharged.

Sources: GLS3, Proposition 1.3.5(c) and Theorem 1.9.5(i);
Borel, III, 9.4--9.5 and IV, 13.15--13.17.
-/

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] [CharP k 2] in
private theorem carrier_connected (Y : ClosedSubgroup K)
    (hY : IsConnected (Y : Set (Variety.Point K))) :
    Variety.IsConnected Y.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph Y.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point K // x ∈ (Y : Set (Variety.Point K))} :=
    Subtype.connectedSpace hY
  let : ConnectedSpace (Variety.Point Y.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- The selected ambient fixed subgroup is one-parameter once the independent
fixed-dimension bound and one-dimensional unipotent classification are supplied. -/
public theorem invariantOneParameterEscape_of_fixedDimensions_of_classification
    (S : Geometry K) (X : ClosedSubgroup K)
    (hXc : IsConnected (X : Set (Variety.Point K)))
    (hXt : IsClosedSubgroupInvariant S.torus X)
    (hXu : IsUnipotentAlgebraicGroup X.carrierVariety)
    (hproper : (containedRootSubgroup S X).toSubgroup < X.toSubgroup)
    (hdim : ∀ q : OneParameterEscape.FixedIndex S,
      Variety.dimension (OneParameterEscape.fixedSubgroup S X q).carrierVariety ≤ 1)
    (hclass : ∀ (Y : Variety k) [AlgebraicGroup Y],
      Variety.IsConnected Y → Variety.dimension Y = 1 →
      IsUnipotentAlgebraicGroup Y → IsOneParameterGroup Y) :
    ∃ Y : ClosedSubgroup K, IsClosedSubgroupInvariant S.torus Y ∧
      IsOneParameterGroup Y.carrierVariety ∧ Y.toSubgroup ≤ X.toSubgroup ∧
      ¬ Y.toSubgroup ≤ (containedRootSubgroup S X).toSubgroup := by
  obtain ⟨q, hq⟩ := OneParameterEscape.exists_fixedSubgroup_not_le S X hXc hXt hproper
  have hpos := OneParameterEscape.escaping_fixedSubgroup_dimension_pos S X hXc hXt hXu q hq
  have hone : Variety.dimension (OneParameterEscape.fixedSubgroup S X q).carrierVariety = 1 :=
    le_antisymm (hdim q) (Cardinal.one_le_iff_ne_zero.mpr hpos.ne')
  refine ⟨OneParameterEscape.fixedSubgroup S X q,
    OneParameterEscape.fixedSubgroup_invariant S X hXt q, ?_,
    OneParameterEscape.fixedSubgroup_le S X q, hq⟩
  exact hclass _
    (carrier_connected _ (OneParameterEscape.fixedSubgroup_connected S X hXc hXt hXu q))
    hone (OneParameterEscape.fixedSubgroup_unipotent S X hXu q)

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
