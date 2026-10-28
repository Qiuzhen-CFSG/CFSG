module
public import Theory.GroupAction.FourElementInvolutionLines
/-!
For an automorphism of square one on a finite elementary binary group,
the module order is the product of its fixed and displacement orders,
and the displacement subgroup is contained in the fixed subgroup.
Consequently the square of the displacement order is at most the module
order. The identity automorphism is included.

The nonidentity case is the cyclic order-two action count; the identity
case has full fixed subgroup and trivial displacement. The squared bound
then follows from the subgroup cardinal inequality. This elementary
rank-nullity calculation is used in both cost branches of Stellmacher
(8.6), printed pp.44–45, and is independent of the local graph setup.
-/

namespace MulAut
open scoped IsMulCommutative
public theorem involution_fixed_displacement_card_data
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (hsquare : a ^ 2 = 1) :
    Nat.card V = Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) V) *
      Nat.card (commutatorAction (Subgroup.zpowers a) V) ∧
      commutatorAction (Subgroup.zpowers a) V ≤
        FixedPoints.subgroup (Subgroup.zpowers a) V := by
  by_cases hone : a = 1
  · have hfixed : FixedPoints.subgroup (Subgroup.zpowers a) V = ⊤ := by
      apply top_unique
      intro point _ mover
      have hmover : (mover : MulAut V) = 1 := by
        obtain ⟨power,hpower⟩ := mover.property
        simpa only [hone, one_zpow] using hpower.symm
      change (mover : MulAut V) point = point
      rw [hmover]
      rfl
    have hcomm : commutatorAction (Subgroup.zpowers a) V = ⊥ := by
      apply bot_unique
      rw [commutatorAction_eq_closure, Subgroup.closure_le]
      rintro _ ⟨mover,point,rfl⟩
      have hmover : (mover : MulAut V) = 1 := by
        obtain ⟨power,hpower⟩ := mover.property
        simpa only [hone, one_zpow] using hpower.symm
      change point⁻¹ * (mover : MulAut V) point = 1
      rw [hmover]
      exact inv_mul_cancel point
    rw [hfixed, hcomm]
    constructor
    · simp only [Nat.card_congr Subgroup.topEquiv.toEquiv, Subgroup.card_bot, mul_one]
    · exact bot_le
  · let _ : Nontrivial V := by
      apply not_subsingleton_iff_nontrivial.mp
      intro hsub
      let _ := hsub
      apply hone
      ext x
      exact Subsingleton.elim _ _
    let generator : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
    have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
      ⟨fun h => hone (congrArg Subtype.val h), Subtype.ext hsquare⟩
    have hcyclic : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hsquare hone]
    exact card_two_action_fixed_commutator_card_data
      (U := V) generator hgenerator hcyclic

public theorem displacement_card_sq_le_card
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (hsquare : a^2=1) :
    Nat.card (commutatorAction (Subgroup.zpowers a) V)^2 ≤ Nat.card V := by
  obtain ⟨hcount,hle⟩ := involution_fixed_displacement_card_data a hsquare
  have hcard := Subgroup.card_le_of_le hle
  rw [hcount,pow_two]
  exact Nat.mul_le_mul_right _ hcard
end MulAut
