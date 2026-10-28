module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.Inputs

/-!
# The chosen Borel's internal torus and unipotent factors

To apply solvable semisimple conjugacy to the Borel supplied by `Geometry`,
its torus and unipotent radical must be regarded as closed subgroups of the
Borel carrier. This module constructs those subgroups by inverse image under
the inclusion and proves their torus, connectedness, unipotence, relative
normality, and pointwise factorization properties. Connectedness of the
supplied radical follows by uniqueness from the connected radical existence
theorem; normality is used only inside the Borel.

These are the local inputs for the semisimple-containment argument. Passage
from an arbitrary ambient element into the chosen Borel remains a separate
geometric obligation; no ambient semisimple-containment theorem is asserted
here yet.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, 1.4.2(e), 1.5.1 and 1.6.3;
Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, (6.2)(b) and the proof of 14.8(a).
-/

open Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private lemma carrier_connected (H : ClosedSubgroup K)
    (hH : _root_.IsConnected (H : Set (Variety.Point K))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point K // x ∈ (H : Set (Variety.Point K))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private abbrev inside (H B : ClosedSubgroup K) : ClosedSubgroup B.carrierVariety :=
  B.inclusion.closedSubgroupPreimage H

private def into (H B : ClosedSubgroup K) (hHB : H ≤ B) :
    Theory.AlgebraicGroup.Morphism H.carrierVariety B.carrierVariety :=
  H.inclusion.codRestrictClosedSubgroup B fun h => hHB (H.pointEquiv h).property

omit [IsAlgClosed k] in
private lemma into_apply (H B : ClosedSubgroup K) (hHB : H ≤ B)
    (h : Variety.Point H.carrierVariety) :
    B.inclusion.onPoints ((into H B hHB).onPoints h) = H.inclusion.onPoints h :=
  H.inclusion.codRestrictClosedSubgroup_inclusion_apply B
    (fun h => hHB (H.pointEquiv h).property) h

private lemma inside_eq_image (H B : ClosedSubgroup K) (hHB : H ≤ B) :
    inside H B = (into H B hHB).imageClosedSubgroup := by
  apply SetLike.coe_injective
  apply Set.ext
  intro x
  change B.inclusion.onPoints x ∈ H.toSubgroup ↔
    ∃ h, (into H B hHB).onPoints h = x
  constructor
  · intro hx
    let h := H.pointEquiv.symm ⟨B.inclusion.onPoints x, hx⟩
    refine ⟨h, B.inclusion_injective ?_⟩
    rw [into_apply]
    exact congrArg Subtype.val (H.pointEquiv.apply_symm_apply _)
  · rintro ⟨h, rfl⟩
    rw [into_apply]
    exact (H.pointEquiv h).property

/-- Restricting a supplied torus-unipotent decomposition to the actual Borel
carrier preserves its connected unipotent factor and relative normality. -/
public theorem borel_internal_factors (B T U : ClosedSubgroup K)
    (hB : IsBorelSubgroup B) (hT : IsSubtorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf B U)
    (hfactor : ∀ x ∈ B.toSubgroup, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u) :
    letI := (B.inclusion.closedSubgroupPreimage U).carrierAlgebraicGroup
    IsSubtorus (B.inclusion.closedSubgroupPreimage T) ∧
      Variety.IsConnected (B.inclusion.closedSubgroupPreimage U).carrierVariety ∧
      IsUnipotentAlgebraicGroup (B.inclusion.closedSubgroupPreimage U).carrierVariety ∧
      (B.inclusion.closedSubgroupPreimage U).toSubgroup.Normal ∧
      ∀ x : Variety.Point B.carrierVariety, ∃ t u,
        t ∈ (B.inclusion.closedSubgroupPreimage T).toSubgroup ∧ u ∈ (B.inclusion.closedSubgroupPreimage U).toSubgroup ∧ x = t * u := by
  let := (inside U B).carrierAlgebraicGroup
  have hTI : IsSubtorus (inside T B) := by
    rw [inside_eq_image T B hTB]
    exact morphism_image_isTorus (into T B hTB) hT
  have hUconn : _root_.IsConnected (U : Set (Variety.Point K)) := by
    obtain ⟨V, hV, hVconn⟩ :=
      exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
    rwa [unipotent_radical_unique hV hU] at hVconn
  have hUIconn : Variety.IsConnected (inside U B).carrierVariety := by
    rw [inside_eq_image U B hU.1]
    exact carrier_connected _
      ((into U B hU.1).imageClosedSubgroup_isConnected (carrier_connected U hUconn))
  let f := into U B hU.1
  have hfmem (u : Variety.Point U.carrierVariety) :
      f.onPoints u ∈ (inside U B).toSubgroup := by
    change B.inclusion.onPoints (f.onPoints u) ∈ U.toSubgroup
    rw [into_apply]
    exact (U.pointEquiv u).property
  let q := f.codRestrictClosedSubgroup (inside U B) hfmem
  have hqsurj : Function.Surjective q.onPoints := by
    intro x
    have hx : (inside U B).inclusion.onPoints x ∈ f.imageClosedSubgroup := by
      rw [← inside_eq_image U B hU.1]
      exact ((inside U B).pointEquiv x).property
    obtain ⟨u, hu⟩ := hx
    refine ⟨u, (inside U B).inclusion_injective ?_⟩
    rw [Theory.AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hu
  have hUI : IsUnipotentAlgebraicGroup (inside U B).carrierVariety :=
    hU.2.1.of_surjective q hqsurj
  have hnormal : (inside U B).toSubgroup.Normal := by
    constructor
    intro x hx b
    change B.inclusion.onPoints (b * x * b⁻¹) ∈ U.toSubgroup
    rw [map_mul, map_mul, map_inv]
    exact hU.2.2.1 _ (B.pointEquiv b).property _ hx
  refine ⟨hTI, hUIconn, hUI, hnormal, ?_⟩
  intro x
  obtain ⟨t, u, ht, hu, htu⟩ :=
    hfactor (B.inclusion.onPoints x) (B.pointEquiv x).property
  let tB := B.pointEquiv.symm ⟨t, hTB ht⟩
  let uB := B.pointEquiv.symm ⟨u, hU.1 hu⟩
  have htB : B.inclusion.onPoints tB = t :=
    congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
  have huB : B.inclusion.onPoints uB = u :=
    congrArg Subtype.val (B.pointEquiv.apply_symm_apply _)
  refine ⟨tB, uB, ?_, ?_, B.inclusion_injective ?_⟩
  · change B.inclusion.onPoints tB ∈ T.toSubgroup
    rwa [htB]
  · change B.inclusion.onPoints uB ∈ U.toSubgroup
    rwa [huB]
  · rw [map_mul, htB, huB]
    exact htu

variable [CharP k 2]

/-- The supplied positive-Borel witness discharges every factorization premise
of the solvable semisimple-conjugacy theorem on the Borel carrier. -/
public theorem chosen_borel_internal_factors (S : Geometry K) :
    let B := S.bigCell.data.B
    let T := B.inclusion.closedSubgroupPreimage S.torus
    let U := B.inclusion.closedSubgroupPreimage S.bigCell.data.positive_witness.unipotent
    letI := U.carrierAlgebraicGroup
    IsSubtorus T ∧ Variety.IsConnected U.carrierVariety ∧
      IsUnipotentAlgebraicGroup U.carrierVariety ∧ U.toSubgroup.Normal ∧
      ∀ x : Variety.Point B.carrierVariety, ∃ t u,
        t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
  apply borel_internal_factors S.bigCell.data.B S.torus
    S.bigCell.data.positive_witness.unipotent S.bigCell.data.B_isBorel
    S.maximalTorus.1 S.bigCell.torus_le_positive S.bigCell.data.positive_witness.radical
  intro x hx
  obtain ⟨t, u, ht, hu, hxu⟩ := (S.bigCell.positive_decomposition x).mp hx
  refine ⟨t, u, ht, ?_, hxu⟩
  rw [S.bigCell.data.positive_witness.root_generated]
  exact hu

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
