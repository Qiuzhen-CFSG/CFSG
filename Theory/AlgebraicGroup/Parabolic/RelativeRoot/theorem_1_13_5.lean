module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.theorem_1_13_3

/-!
This module isolates `theorem_1_13_5` from `Theory.AlgebraicGroup.Parabolic.RelativeRoot`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 800000 in
public theorem theorem_1_13_5
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
    S.U.toSubgroup = S.layer 1 ∧
    S.layer (S.maxRelativeHeight + 1) = ⊥ ∧
    Group.nilpotencyClass S.U.toSubgroup ≤ S.maxRelativeHeight ∧
    (∀ i, 0 < i → ⁅S.layer i, S.U.toSubgroup⁆ ≤ S.layer (i + 1)) ∧
    (∀ i, S.P.toSubgroup ≤ Subgroup.normalizer
      (S.layer i : Set (Variety.Point K))) ∧
    (∀ i, 0 < i → S.layer i ≤ S.U.toSubgroup) ∧
    (∀ i, 0 < i →
      ((S.layer i).subgroupOf S.U.toSubgroup).Normal) ∧
    (∀ classification, HasDynkinType S.rootPairing classification →
      ¬ IsUSingular classification (ringChar k) →
      ∀ i, 0 < i →
        S.layer i = S.U.toSubgroup.lowerCentralSeries (i - 1)) ∧
    (∀ classification, HasDynkinType S.rootPairing classification →
      ¬ IsUSingular classification (ringChar k) →
      ∀ i, i ≤ S.maxRelativeHeight →
        Subgroup.map S.U.toSubgroup.subtype
          (Subgroup.upperCentralSeries S.U.toSubgroup i) =
          S.layer (S.maxRelativeHeight + 1 - i)) ∧
    (∀ i, 0 < i →
      ∃ hle : S.layer (i + 1) ≤ S.layer i,
      ∃ hnormal : ((S.layer (i + 1)).subgroupOf (S.layer i)).Normal,
        Nonempty (RelativeRootLayerQuotientModel S i hle hnormal)) ∧
    Nonempty
      (LeviCenterQuotientTorusModel S.L
        (Nat.card { α : S.D.Root // α ∈ S.D.simple \ S.J })) ∧
    (∀ α β,
      RelativeRootProjection S.coeff S.base.support (S.rootEquiv '' S.J)
          (S.rootEquiv α) =
        RelativeRootProjection S.coeff S.base.support (S.rootEquiv '' S.J)
          (S.rootEquiv β) →
      ∀ z, z ∈ Subgroup.map S.L.toSubgroup.subtype
        (Subgroup.center S.L.toSubgroup) →
      ∃ c : kˣ, ∀ t : k,
        z⁻¹ * S.C.x α t * z = S.C.x α ((c : k) * t) ∧
        z⁻¹ * S.C.x β t * z = S.C.x β ((c : k) * t)) ∧
    (∀ l, l ∈ S.L →
      ((∀ u, u ∈ S.U → l⁻¹ * u * l = u) ↔
        l ∈ Subgroup.center (Variety.Point K))) ∧
    (∀ l, l ∈ S.L →
      ((∀ u, u ∈ S.U → l⁻¹ * u * l * u⁻¹ ∈ S.layer 2) ↔
        l ∈ Subgroup.center (Variety.Point K))) := by sorry

end Theory.AlgebraicGroup
