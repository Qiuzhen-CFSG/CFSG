module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.MovedPoints
public import Theory.SpecificGroups.Held.Model.Perfect
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Faithfulness

/-!
# The explicit Held involution is outer

The representative is fixed-point-free on 2058 letters, so its sign is
negative. Every element of Held is even because Held is perfect. Faithfulness
of the full normalizer action therefore rules out an inner induced action.
Source: ATLAS `HeG1-a2W1` on the exact degree-2058 Held permutation model.
-/

public section
namespace Held.OuterInvolution
private theorem sign_of_free_involution (σ : Equiv.Perm (Fin 2058))
    (hs : σ ^ 2 = 1) (hf : ∀ x, σ x ≠ x) : Equiv.Perm.sign σ = -1 := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one hs]
  let : IsEmpty (Function.fixedPoints σ) := ⟨fun x => hf x.val x.property⟩
  simp only [Fintype.card_eq_zero, Fintype.card_fin, Nat.sub_zero]
  exact (by decide : Odd (1029 : ℕ)).neg_one_pow

theorem representative_sign :
    Equiv.Perm.sign (representative : Equiv.Perm (Fin 2058)) = -1 := by
  apply sign_of_free_involution _ _ representative_no_fixed_points
  change (implementer ^ 5) ^ 2 = 1
  rw [← pow_mul]
  exact tenth_power

private theorem sign_eq_one_of_mem (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ permutationGroup) : Equiv.Perm.sign σ = 1 := by
  have h := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) ⟨σ, hσ⟩
  simpa only [MonoidHom.comp_apply, representation, Subgroup.subtype_apply] using h

/-- This specific order-two action is not inner. -/
theorem action_not_inner : ¬ ∃ g : He, MulAut.conj g = action := by
  intro h
  have hm := (normalizer_action_inner_iff representative).mp h
  have heven := sign_eq_one_of_mem _ hm
  rw [representative_sign] at heven
  exact (by decide : (-1 : ℤˣ) ≠ 1) heven

end Held.OuterInvolution
