module

public import Stellmacher.C4QuaternionFactorCharacteristic
public import Stellmacher.QuaternionResidualActionCollapse

/-!
# Nontrivial residual action on C4 central Q8

Extract the actual quaternion factor from the central-product model. Its
intrinsic invariance and index two put every normalizer commutator in that
factor. The commuting-factor cardinal formula makes the whole a two-group,
so residual commutator idempotence applies. A nontrivial idempotent residual
action cannot be contained in a proper cyclic subgroup of the quaternion
factor, and hence the commutator equals that factor.

This supplies the raw action recognition used in Stellmacher (1997),
printed p.41, (8.6)(a2), and the small-V paragraph on printed p.42.
-/

namespace Stellmacher
open Later
universe u

private theorem c4_quaternion_model_isTwoGroup
    {G : Type u} [Group G] [Finite G] (whole : Subgroup G)
    (hmodel : IsCentralProductModel whole C4 Q8) : IsPGroup 2 whole := by
  obtain ⟨left, right, ⟨leftModel⟩, ⟨rightModel⟩, rfl, hintersection, hcommute, _⟩ := hmodel
  have hnormalize : right ≤ Subgroup.normalizer (left : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro actor hactor element helement
    exact hcommute element helement actor hactor
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    left right hnormalize
  rw [Nat.card_congr leftModel.toEquiv, Nat.card_congr rightModel.toEquiv,
    hintersection] at hcard
  have hcyclic : Nat.card C4 = 4 := by simp [C4]
  have hquaternion : Nat.card Q8 = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hcyclic, hquaternion] at hcard
  apply IsPGroup.of_card (n := 4)
  omega

public theorem c4_quaternion_nontrivial_residual_commutator_model
    {G : Type u} [Group G] [Finite G]
    (whole actors : Subgroup G)
    (hmodel : IsCentralProductModel whole C4 Q8)
    (hnormalize : actors ≤ Subgroup.normalizer (whole : Set G))
    (hnontrivial : ⁅whole, twoResidualAmbient actors⁆ ≠ ⊥) :
    IsModel (⁅whole, twoResidualAmbient actors⁆) Q8 := by
  obtain ⟨container, hcontainer, _, _, hbound⟩ :=
    c4_quaternion_model_exists_commutator_bound whole actors hmodel hnormalize
  have hresidual : twoResidualAmbient actors ≤ actors := Subgroup.map_subtype_le _
  have hcontain : ⁅whole, twoResidualAmbient actors⁆ ≤ container :=
    (Subgroup.commutator_mono le_rfl hresidual).trans hbound
  have hequal := quaternion_nontrivial_residual_commutator_eq whole actors container
    hcontainer (c4_quaternion_model_isTwoGroup whole hmodel) hnormalize hcontain hnontrivial
  exact hequal.symm ▸ hcontainer

end Stellmacher
