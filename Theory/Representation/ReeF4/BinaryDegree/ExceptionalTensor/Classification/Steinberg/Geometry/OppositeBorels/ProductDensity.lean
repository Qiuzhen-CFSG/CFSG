module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Candidates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.ProductDensity.GeometricCriterion
public import Theory.AlgebraicGroup.ClosedSubgroup.Product

/-!
# Density of the literal F4 opposite product

The split-torus tangent and the 48 root tangents span the actual carrier:
their independence and the proved dimension bound force equality. Each root
tangent factors through its signed candidate, so the multiplication map has
surjective differential and dense image. Connectedness makes the carrier
irreducible, hence this product of closed subgroups is also open.

This proves the density/open-product portion of Steinberg (6.2)(c)
(`refs/KGroup/GLS3/Chapter2St2.tex`). It does not assume Borel maximality,
unipotence or the opposite-intersection statement. The general density
criterion is imported from its existing extension, independently of Spin.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.F4Chevalley
open scoped Pointwise
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
open RootModel.Corrected
universe u
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]
local instance densitySubgroupAlgebraicGroup
    (H : ClosedSubgroup (Carrier (k := F))) : AlgebraicGroup H.carrierVariety :=
  H.carrierAlgebraicGroup

omit [CharP F 2] in
private theorem tangent_range_mono {H J : ClosedSubgroup (Carrier (k := F))}
    (h : H ≤ J) :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap H.inclusion) ≤
      LinearMap.range (Bor1.identityTangentMorphismLinearMap J.inclusion) := by
  let j := H.inclusion.codRestrictClosedSubgroup J
    (fun x => h (H.pointEquiv x).property)
  have hj : J.inclusion.comp j = H.inclusion := by
    apply Morphism.ext
    funext x
    exact (Morphism.codRestrictClosedSubgroup_inclusion_apply H.inclusion J
      (fun y => h (H.pointEquiv y).property) x).symm
  rintro v ⟨w, rfl⟩
  refine ⟨Bor1.identityTangentMorphismLinearMap j w, ?_⟩
  rw [← LinearMap.comp_apply, ← Bor1.identityTangentMorphismLinearMap_comp, hj]

/-- The actual torus tangent, rather than just the entire fixed space,
together with the literal root tangents spans the F4 carrier. -/
theorem torus_root_tangent_span :
    concreteTorusTangentRange (k := F) ⊔ concreteRootTangentSpan = ⊤ := by
  apply Submodule.eq_top_of_disjoint
  · rw [concreteTorusTangentRange_finrank, concreteRootTangentSpan_finrank]
    exact concreteIdentityTangent_finrank_le_torus_add_card_root
  · exact concreteFixedTangent_disjoint_rootTangentSpan.mono_left
      concreteTorusTangentRange_le_fixed

/-- The positive root group and negative torus/root group supply every
identity tangent direction, without a Borel premise. -/
theorem positiveUnipotent_negativeCandidate_tangent_span :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap (positiveUnipotent F).inclusion) ⊔
      LinearMap.range (Bor1.identityTangentMorphismLinearMap (negativeCandidate F).inclusion) =
        ⊤ := by
  apply top_unique
  rw [← torus_root_tangent_span F]
  apply sup_le
  · exact (tangent_range_mono F (torus_le_torusRootGenerated F (negativeRoots F))).trans
      le_sup_right
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    have hr : (⟨r⟩ : Roots F) ∈ positiveRoots F ∪ negativeRoots F := by
      rw [positive_union_negative]
      exact Set.mem_univ _
    have ht := oneParameterTangent_mem_range_inclusion
      (rootSubgroup (k := F) r) (rootParametrization r)
    rcases hr with hr | hr
    · apply Submodule.mem_sup_left
      exact tangent_range_mono F
        (show rootSubgroup r ≤ positiveUnipotent F from
          rootSubgroup_le_RootSubgroupGenerated (rootSystemModel (F := F)).rootData hr) ht
    · apply Submodule.mem_sup_right
      apply tangent_range_mono F
        (show rootSubgroup r ≤ negativeCandidate F from
          fun x hx => rootGenerated_le_torusRootGenerated F (negativeRoots F)
            (rootSubgroup_le_RootSubgroupGenerated (rootSystemModel (F := F)).rootData hr hx)) ht

/-- The opposite product is dense in the literal F4 carrier. -/
theorem positiveUnipotent_negativeCandidate_product_dense :
    Dense (((positiveUnipotent F).toSubgroup : Set (Variety.Point (Carrier (k := F)))) *
      ((negativeCandidate F).toSubgroup : Set (Variety.Point (Carrier (k := F))))) :=
  Bor1.closedSubgroup_product_dense_of_tangent_span
    (positiveUnipotent F) (negativeCandidate F) carrier_isConnected
    (positiveUnipotent_negativeCandidate_tangent_span F)

/-- The two closed torus/root candidates also have dense product. -/
theorem candidates_product_dense :
    Dense (((positiveCandidate F).toSubgroup : Set (Variety.Point (Carrier (k := F)))) *
      ((negativeCandidate F).toSubgroup : Set (Variety.Point (Carrier (k := F))))) := by
  apply (positiveUnipotent_negativeCandidate_product_dense F).mono
  exact Set.mul_subset_mul
    (fun _ hx => rootGenerated_le_torusRootGenerated F (positiveRoots F) hx)
    (Set.Subset.refl _)

/-- The dense opposite product is open in the actual connected carrier. -/
theorem candidates_product_open :
    IsOpen (((positiveCandidate F).toSubgroup : Set (Variety.Point (Carrier (k := F)))) *
      ((negativeCandidate F).toSubgroup : Set (Variety.Point (Carrier (k := F))))) := by
  let : PreirreducibleSpace (Variety.Point (Carrier (k := F))) :=
    ⟨(connectedAlgebraicGroup_irreducible (Carrier (k := F)) carrier_isConnected).2⟩
  exact closedSubgroup_product_isOpen_of_dense (positiveCandidate F) (negativeCandidate F)
    (candidates_product_dense F)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
