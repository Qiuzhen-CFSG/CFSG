module

public import Theory.AlgebraicGroup.RootSubgroups.ReducedCurveIntegrability
public import Theory.AlgebraicGroup.Semisimple.RootBlocks

/-!
# Root-tangent integrability inside a connected root block

This module specializes the characteristic-sensitive one-parameter integrability
criterion to a closed subgroup of a connected root block.  The closed subgroup
is first mapped into the ambient algebraic group.  If a chosen root
parametrization has tangent in the differential range of that closed image and
its pullbacks satisfy the relative Frobenius-saturation condition, then the
whole ambient root subgroup lies in the image of the block subgroup.

The saturation hypothesis is essential in positive characteristic: ordinary
tangent containment alone cannot distinguish a purely inseparable Frobenius
curve.  The proof applies the reduced-curve criterion to the ambient closed
image, then uses surjectivity of the one-parameter parametrization to pass from
its scalar range to every root-subgroup point.  No source-numbered structural
theorem is used.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/--
A root subgroup is contained in the ambient image of a closed subgroup of its
connected root block when its chosen parameter tangent belongs to the
differential range of that image and the parameter is Frobenius-saturated
relative to its vanishing ideal.
-/
public theorem rootSubgroup_le_connectedRootBlockSubgroup_image_of_tangent_mem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {iota : Type u}
    (e : D.Root ≃ iota) (s : Set iota) (alpha : D.Root)
    (N : ClosedSubgroup
      (connectedRootBlockSubgroup D (e.symm '' s)).carrierVariety)
    (x : OneParameterParametrization
      (D.rootSubgroup alpha).carrierVariety) :
    letI := N.carrierAlgebraicGroup
    oneParameterTangent (D.rootSubgroup alpha) x ∈
        LinearMap.range (identityTangentMorphismLinearMap
          ((connectedRootBlockSubgroup D (e.symm '' s)).inclusion.comp
            N.inclusion).imageClosedSubgroup.inclusion) →
      OneParameterVanishingFrobeniusSaturated
          ((connectedRootBlockSubgroup D (e.symm '' s)).inclusion.comp
            N.inclusion).imageClosedSubgroup
          (D.rootSubgroup alpha) x →
        (D.rootSubgroup alpha).toSubgroup ≤
          N.toSubgroup.map
            (connectedRootBlockSubgroup D (e.symm '' s)).inclusion.onPoints := by
  let _ := N.carrierAlgebraicGroup
  intro htangent hsaturated
  let H := connectedRootBlockSubgroup D (e.symm '' s)
  let J := (H.inclusion.comp N.inclusion).imageClosedSubgroup
  have hrange : Set.range (fun t : k =>
      (D.rootSubgroup alpha).includePoint (x.value t)) ⊆
      (J.toSubgroup : Set (Variety.Point K)) :=
    oneParameter_range_le_of_tangent_mem_of_vanishingFrobeniusSaturated
      J (D.rootSubgroup alpha) x htangent hsaturated
  intro g hg
  have hgRange : g ∈ Set.range (D.rootSubgroup alpha).inclusion.onPoints := by
    rw [(D.rootSubgroup alpha).range_inclusion]
    exact hg
  obtain ⟨z, rfl⟩ := hgRange
  obtain ⟨a, rfl⟩ := x.toMulEquiv.surjective z
  let t : k := Multiplicative.toAdd (additiveGroupPointEquiv k a)
  have ha : kPlusPoint t = a := by
    apply (additiveGroupPointEquiv k).injective
    simp [t, kPlusPoint]
  have hinc (z : Variety.Point (D.rootSubgroup alpha).carrierVariety) :
      (D.rootSubgroup alpha).includePoint z =
        (D.rootSubgroup alpha).inclusion.onPoints z := by
    apply Variety.Point.ext
    funext i
    rfl
  have hj := hrange ⟨t, by
    change (D.rootSubgroup alpha).includePoint (x.hom.onPoints (kPlusPoint t)) =
      (D.rootSubgroup alpha).inclusion.onPoints (x.hom.onPoints a)
    rw [ha, hinc] ⟩
  change (D.rootSubgroup alpha).inclusion.onPoints (x.hom.onPoints a) ∈
    (H.inclusion.comp N.inclusion).image at hj
  rcases hj with ⟨n, hn⟩
  refine ⟨N.inclusion.onPoints n, (N.pointEquiv n).property, ?_⟩
  exact hn

end Theory.AlgebraicGroup
