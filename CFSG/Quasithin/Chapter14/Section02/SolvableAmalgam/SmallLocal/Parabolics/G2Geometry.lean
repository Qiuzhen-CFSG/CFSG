module

public import Theory.AtlasPort.LinearGroups.G2.BinaryNaturalPlane
public import Theory.GroupAction.ResidualMovingPointTransport

/-!
# Concrete input calculations for the small parabolic pairs

For the split-octonion model of G₂(2), the five-root subgroup has two
compatible quaternion factors, order 32, and extraspecial structure. The
second parabolic contains a normal elementary eight, its natural four, and
a residual cubic moving the distinguished involution. The latter witness
transports along an isomorphism of the second parabolic itself.

This lower interface retains the original elementary-subgroup calculations.
The first-core and Sylow identifications are assembled in `Parabolics.G2`;
`Parabolics` re-exports the complete G₂ and M₁₂ inputs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Hypothesis 14.2.1 and Lemma 14.2.21, printed pp.981 and 988 (PDF p.1005).
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics

open Atlas.G2 Atlas.G2.BinaryCore

/-- The quaternion factors are embedded in the actual root-defined subgroup. -/
public noncomputable def g2_core_factors : Subgroup.QuaternionCentralProductData core :=
  coreQuaternionData

/-- The marked elementary subgroups and point inside the actual G₂(2) model. -/
public theorem g2_elementary_geometry :
    Nat.card core = 32 ∧ IsExtraspecial 2 core ∧
      Nat.card elementary = 8 ∧ IsElementaryAbelian 2 elementary ∧
      natural ≤ elementary ∧ elementary ≤ core ∧
      Nat.card natural = 4 ∧ z ∈ natural ∧ orderOf z = 2 :=
  ⟨card_core, extraspecial_core, card_elementary, inferInstance,
    natural_le_elementary, elementary_le_core, card_natural, z_mem_natural, z_order⟩

/-- The concrete marked subgroup chain required by the elementary-eight argument. -/
public theorem g2_marked_subgroups :
    Nat.card distinguished = 2 ∧ distinguished ≤ natural ∧
      natural ≤ elementary ∧ elementary ≤ core ∧ elementary ≤ secondParabolic :=
  ⟨card_distinguished, distinguished_le_natural, natural_le_elementary,
    elementary_le_core, elementary_le_secondParabolic⟩

/-- The second parabolic normalizes both marked elementary subgroups and
contains an actual residual element moving the distinguished involution. -/
public theorem g2_secondParabolic_action :
    Nat.card secondParabolic = 192 ∧
      (elementary.subgroupOf secondParabolic).Normal ∧
      (natural.subgroupOf secondParabolic).Normal ∧
      orderOf movingActor = 3 ∧
      ∃ y : secondParabolic, y ∈ pResidual 2 secondParabolic ∧
        (y : Model (ZMod 2)) * z * (y : Model (ZMod 2))⁻¹ ≠ z :=
  ⟨secondParabolic_card, inferInstance, inferInstance, movingActor_order,
    ⟨movingActor, movingActor_mem⟩, movingActor_residual, movingActor_moves⟩

/-- The moving-point calculation only needs an isomorphism of the second
parabolic; no ambient-group isomorphism or global recognition is assumed. -/
public theorem g2_moving_point_transport {A : Type*} [Group A]
    (e : secondParabolic ≃* A) :
    let E := (elementary.subgroupOf secondParabolic).map e.toMonoidHom
    let zA := e ⟨z, elementary_le_secondParabolic z_mem_elementary⟩
    zA ∈ E ∧ ∃ y : A, y ∈ pResidual 2 A ∧
      y ∈ Subgroup.normalizer (E : Set A) ∧ y * zA * y⁻¹ ≠ zA := by
  let z₀ : secondParabolic := ⟨z, elementary_le_secondParabolic z_mem_elementary⟩
  let y₀ : secondParabolic := ⟨movingActor, movingActor_mem⟩
  have hz₀ : z₀ ∈ elementary.subgroupOf secondParabolic := z_mem_elementary
  have hn : y₀ ∈ Subgroup.normalizer
      (elementary.subgroupOf secondParabolic : Set secondParabolic) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hm : y₀ * z₀ * y₀⁻¹ ≠ z₀ := by
    intro h
    exact movingActor_moves (congrArg Subtype.val h)
  obtain ⟨hz, hy, hnorm, hmove⟩ := Subgroup.map_residual_moving_point e
    (elementary.subgroupOf secondParabolic) z₀ hz₀ y₀ movingActor_residual hn hm
  exact ⟨hz, e y₀, hy, hnorm, hmove⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics
