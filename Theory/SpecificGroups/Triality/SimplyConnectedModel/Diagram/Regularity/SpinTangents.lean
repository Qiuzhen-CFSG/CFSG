module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.SpinTangents.OrthogonalBound
public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Independence

/-!
# Torus and root tangents span the concrete Clifford Spin D4 tangent

The regular Spin cover has finite kernel and exact Omega image, so the
kernel–image dimension formula and smoothness of algebraic groups identify
their tangent dimensions. The quadratic-isometry matrix equations bound the
Omega tangent dimension by 28. The actual coroot-coordinate isomorphism
makes the Spin torus tangent four-dimensional, and the 24 realized roots
supply independent nontrivial weight directions disjoint from that tangent.
The matching bounds therefore prove the requested spanning equality.

This uses neither tangent injectivity of the Spin cover nor a regular inverse
to its point-group equivalence. It concerns the published Clifford carrier and
the pinned closed torus and root subgroups, with no additional geometry premise.

Sources: GLS3, Chapter 1, §§1.9–1.14; Steinberg (6.2)(b–c) in
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The genuine simple-coroot coordinate isomorphism gives four torus directions. -/
theorem corootTorus_tangent_finrank :
    Module.finrank k (Bor1.IdentityPointDerivation (CorootTorus.closedSubgroup k).carrierVariety) = 4 := by
  rw [Bor1.identityPointDerivation_finrank_eq_dimension]
  have hdim := algebraicGroupIso_dimension_eq (CorootTorus.coordinateIso k)
  rw [dVariety_dimension_eq] at hdim
  simpa using congrArg Cardinal.toNat hdim.symm

/-- The actual Spin D4 root datum has 24 roots. -/
theorem pinnedRootData_card : Nat.card (pinnedRootData k).Root = 24 := by
  change Nat.card (ULift RootIndex) = 24
  rw [Nat.card_ulift]
  have hsign : Nat.card ({-1, 1} : Set ℝ) = 2 := by
    norm_num [Set.ncard_insert_of_notMem]
  have hpairs : Nat.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  change Nat.card ({p : Fin 4 × Fin 4 // p.1 < p.2} ×
    ({-1, 1} : Set ℝ) × ({-1, 1} : Set ℝ)) = 24
  rw [Nat.card_prod, Nat.card_prod, hsign, hpairs]

omit [CharP k 2] in
/-- The regular finite-kernel Spin cover preserves variety dimension. -/
theorem spin_dimension_eq_omega :
    Variety.dimension (groupVariety k) =
      Variety.dimension (cliffordModel k).omega.carrierVariety := by
  let f := (cliffordModel k).spinCover
  have hf := (cliffordModel k).spinCoverIsogeny
  have hkernelPoints : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety) := by
    apply (Equiv.finite_iff f.kernelClosedSubgroup.pointEquiv).mpr
    change Finite f.kernel
    exact hf.2
  have hkernelDimension : Variety.dimension f.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points f.kernelClosedSubgroup.carrierVariety).2 hkernelPoints
  have himageDimension : Variety.dimension f.imageClosedSubgroup.carrierVariety =
      Variety.dimension (cliffordModel k).omega.carrierVariety := by
    apply (closedSubgroup_dimension_eq_iff_contains_identityComponent
      _ f.imageClosedSubgroup).2
    intro y _
    change y ∈ f.image
    exact hf.1 y
  have hdimension := morphism_dimension_eq_kernel_add_image f
  simpa only [hkernelDimension, himageDimension, zero_add] using hdimension

omit [CharP k 2] in
/-- Smoothness turns the isogeny dimension equality into equality of tangent
 dimensions; no assertion about the differential of the cover is required. -/
theorem spin_tangent_finrank_eq_omega :
    Module.finrank k (Bor1.IdentityPointDerivation (groupVariety k)) =
      Module.finrank k (Bor1.IdentityPointDerivation (cliffordModel k).omega.carrierVariety) := by
  rw [Bor1.identityPointDerivation_finrank_eq_dimension,
    Bor1.identityPointDerivation_finrank_eq_dimension, spin_dimension_eq_omega]

omit [CharP k 2] in
/-- The concrete Clifford Spin D4 tangent has dimension at most 28. -/
theorem spin_tangent_finrank_le :
    Module.finrank k (Bor1.IdentityPointDerivation (groupVariety k)) ≤ 28 := by
  rw [spin_tangent_finrank_eq_omega]
  exact evenOrthogonalOmega_four_tangent_finrank_le

/-- The embedded tangents of the actual Spin coroot torus and all 24 pinned
 root subgroups span the identity tangent of the closed Clifford carrier. -/
theorem torus_root_tangent_span :
    LinearMap.range (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
      (⨆ r : RootIndex, LinearMap.range
        (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k r).inclusion)) = ⊤ := by
  have hbound : Module.finrank k (Bor1.IdentityPointDerivation (groupVariety k)) ≤
      Module.finrank k (Bor1.IdentityPointDerivation (CorootTorus.closedSubgroup k).carrierVariety) +
        Nat.card (pinnedRootData k).Root := by
    rw [corootTorus_tangent_finrank, pinnedRootData_card]
    exact spin_tangent_finrank_le k
  let : Finite (pinnedRootData k).Root :=
    Nat.finite_of_card_ne_zero (by rw [pinnedRootData_card]; decide)
  have h := realized_torus_root_tangent_span_of_finrank_le (pinnedRootData k)
    (pinnedRootData_isRealization k) (CorootTorus.isSubtorus k)
    (pinnedRootParametrization k) hbound
  change LinearMap.range (Bor1.identityTangentMorphismLinearMap
      (CorootTorus.closedSubgroup k).inclusion) ⊔
    (⨆ r : ULift RootIndex, LinearMap.range
      (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k r.down).inclusion)) = ⊤ at h
  simpa only [iSup_ulift] using h

end Triality.SimplyConnected.Pinning
