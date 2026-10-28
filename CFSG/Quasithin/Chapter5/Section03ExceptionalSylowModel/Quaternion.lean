module

public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionFactors
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionQuotient

/-!
# The quaternion core in the exceptional branch of §5.3.7

The marked trace kernel Q in UT₃(F₄)⋊C₂ is the central product of the two
explicit quaternion factors B and D. Its marked central involution subgroup
C is its center and its ambient centralizer. The natural image Qbar in T/C
is elementary abelian of order sixteen. Both marked root planes meet Q in
order eight.

The imported coordinate proofs verify the quaternion presentations, factor
commutation and generation, and the square calculation for the quotient.
This module assembles precisely these results for the exceptional Sylow model;
it uses no matrix-amalgam recognition assumptions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660–661 (PDF pp. 677–678).
-/

public section
namespace Matrix.PSL3Four.SylowModel

/-- The concrete quaternion-core structure required in the exceptional branch. -/
theorem quaternionCore_structure :
    Nat.card Q = 32 ∧
    Nonempty (B ≃* QuaternionGroup 2) ∧ Nonempty (D ≃* QuaternionGroup 2) ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧ B ⊔ D = ⊤ ∧
    Nat.card (Subgroup.center Q) = 2 ∧ Nat.card C = 2 ∧
    IsElementaryAbelian 2 Qbar ∧ Nat.card Qbar = 16 ∧
    Function.Surjective coreQuotient ∧ coreQuotient.ker = C.subgroupOf Q ∧
    Subgroup.centralizer (Q : Set T) ≤ Q ∧
    Nat.card (V₁ ⊓ Q : Subgroup T) = 8 ∧ Nat.card (V₂ ⊓ Q : Subgroup T) = 8 :=
  ⟨card_Q, ⟨quaternionBEquiv⟩, ⟨quaternionDEquiv⟩, B_D_commute,
    card_B_inf_D, B_sup_D, card_center_Q, card_C, inferInstance, card_Qbar,
    coreQuotient_surjective, coreQuotient_ker, centralizer_Q_le_Q,
    card_V₁_inf_Q, card_V₂_inf_Q⟩

end Matrix.PSL3Four.SylowModel
