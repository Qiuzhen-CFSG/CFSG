module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.Candidates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.SpinTangents

/-!
# Tangent spanning for the concrete opposite candidates

The positive root-generated subgroup and the negative torus-and-root subgroup
have tangent images spanning the tangent of the Clifford Spin carrier. Each
root tangent factors through the appropriate closed subgroup, and the torus
factors through the negative candidate. Thus the previously established Spin
torus/root tangent spanning theorem applies without any Borel or big-cell
hypothesis. This is a differential input to the big-cell dimension argument,
not a claim of density or maximal solvability.

Source: Steinberg (6.2)(c), `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels
open Theory.AlgebraicGroup Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

local instance subgroupAlgebraicGroup (H : ClosedSubgroup (groupVariety k)) :
    AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup

omit [CharP k 2] in
private theorem tangent_range_mono {H J : ClosedSubgroup (groupVariety k)}
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

/-- The positive unipotent candidate and the negative Borel candidate together
supply every tangent direction of the concrete Spin group. -/
theorem positiveUnipotent_negativeCandidate_tangent_span :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap (positiveUnipotent k).inclusion) ⊔
      LinearMap.range (Bor1.identityTangentMorphismLinearMap (negativeCandidate k).inclusion) =
        ⊤ := by
  apply top_unique
  rw [← torus_root_tangent_span k]
  apply sup_le
  · exact (tangent_range_mono k (torus_le_torusRootGenerated k (negativeRoots k))).trans
      le_sup_right
  · apply iSup_le
    intro r
    have hr : pinnedRootIndex k r ∈ positiveRoots k ∪ negativeRoots k := by
      rw [positive_union_negative]
      exact Set.mem_univ _
    rcases hr with hr | hr
    · exact (tangent_range_mono k
        (show rootClosedSubgroup k r ≤ positiveUnipotent k from
          rootSubgroup_le_RootSubgroupGenerated (pinnedRootData k) hr)).trans le_sup_left
    · apply le_trans _ le_sup_right
      apply tangent_range_mono k
      intro x hx
      apply rootGenerated_le_torusRootGenerated k (negativeRoots k)
      exact rootSubgroup_le_RootSubgroupGenerated (pinnedRootData k) hr hx

/-- The two actual closed candidates also span the ambient tangent. -/
theorem candidates_tangent_span :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap (positiveCandidate k).inclusion) ⊔
      LinearMap.range (Bor1.identityTangentMorphismLinearMap (negativeCandidate k).inclusion) =
        ⊤ := by
  apply top_unique
  rw [← positiveUnipotent_negativeCandidate_tangent_span k]
  exact sup_le_sup
    (tangent_range_mono k (rootGenerated_le_torusRootGenerated k (positiveRoots k))) le_rfl

end Triality.SimplyConnected.OppositeBorels
