module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.InvariantGeneration.ClosedRoots
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput
public import Theory.AlgebraicGroup.RootSubgroups.Generation

/-!
# Reduction of invariant unipotent root generation to closed-subgroup escape

The contained actual root subgroups generate a connected, closed, torus-invariant
subgroup `H`. If `H` is proper, a one-parameter escape theorem gives an invariant
one-parameter subgroup of `X` outside `H`. Its weight is a realized root;
same-weight uniqueness identifies it with the selected actual root subgroup.
This contradicts the definition of `H`.

The escape theorem and root-subgroup uniqueness are explicit geometric inputs.
This module does not yet assert the unconditional generation consequence of
GLS3, Theorem 1.9.5(i), `refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Coordinates.Normalization
noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

/-- Closed-subgroup escape supplies the canonical one-parameter layer used by
the general generation theorem. Closedness and connectedness of the generated
subgroup are proved here, rather than assumed of an abstract subgroup. -/
public theorem invariantOneParameterLayer_of_closedEscape (S : Geometry K)
    (X : ClosedSubgroup K)
    (hEscape : ∀ H : ClosedSubgroup K, H.toSubgroup < X.toSubgroup →
      IsConnected (H : Set (Variety.Point K)) → IsClosedSubgroupInvariant S.torus H →
      ∃ Y : ClosedSubgroup K, IsClosedSubgroupInvariant S.torus Y ∧
        IsOneParameterGroup Y.carrierVariety ∧ Y.toSubgroup ≤ X.toSubgroup ∧
        ¬ Y.toSubgroup ≤ H.toSubgroup) :
    RootSubgroupGenerated S.roots
        {a | (S.roots.rootSubgroup a).toSubgroup ≤ X.toSubgroup} < X.toSubgroup →
      ∃ Y : ClosedSubgroup K, IsClosedSubgroupInvariant S.torus Y ∧
        IsOneParameterGroup Y.carrierVariety ∧ Y.toSubgroup ≤ X.toSubgroup ∧
        ¬ Y.toSubgroup ≤ RootSubgroupGenerated S.roots
          {a | (S.roots.rootSubgroup a).toSubgroup ≤ X.toSubgroup} := by
  intro hproper
  exact hEscape (containedRootSubgroup S X) hproper
    (containedRootSubgroup_connected S X) (containedRootSubgroup_invariant S X)

/-- Root-subgroup uniqueness turns one-parameter escape into generation by the
literal chosen roots. The two extra premises still require geometric proofs. -/
public theorem invariantUnipotentRootGeneration_of_oneParameterEscape_of_unique (S : Geometry K)
    (X : ClosedSubgroup K)
    (hEscape : (containedRootSubgroup S X).toSubgroup < X.toSubgroup →
      ∃ Y : ClosedSubgroup K, IsClosedSubgroupInvariant S.torus Y ∧
        IsOneParameterGroup Y.carrierVariety ∧ Y.toSubgroup ≤ X.toSubgroup ∧
        ¬ Y.toSubgroup ≤ (containedRootSubgroup S X).toSubgroup)
    (hunique : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S) :
    X.toSubgroup = RootSubgroupGenerated S.roots
      {a | (S.roots.rootSubgroup a).toSubgroup ≤ X.toSubgroup} := by
  have hle := containedRootSubgroup_le S X
  apply le_antisymm ?_ hle
  by_contra hnot
  have hproper : RootSubgroupGenerated S.roots
      {a | (S.roots.rootSubgroup a).toSubgroup ≤ X.toSubgroup} < X.toSubgroup :=
    ⟨hle, hnot⟩
  obtain ⟨a, haX, haH⟩ :=
    exists_rootSubgroup_not_le_of_proper_invariant_oneParameter_layer
      S.torus X S.roots S.realized _
      ⟨hproper, hEscape hproper⟩
      (fun {Y} {a} hY hYweight => hunique a Y hY hYweight)
  exact haH (rootSubgroup_le_RootSubgroupGenerated S.roots haX)

end
end ConnectedCentralizer.Bruhat.Coordinates.Normalization
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
