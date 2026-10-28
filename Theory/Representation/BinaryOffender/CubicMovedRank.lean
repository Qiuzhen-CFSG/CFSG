module

public import Theory.Representation.BinaryOffender.SubspaceAction
/-!
# The minimum dimension moved by a cubic subgroup

In a faithful binary action, choose a nonzero displacement d for a cubic
actor a. The vectors d and a(d) are nonzero and distinct: fixing d would
make a have both quadratic and cubic period on the original vector.
Thus the moved space has at least three elements, hence dimension at least
two over F₂. No semisimplicity or splitting of the original module is used.

This elementary bound is used with the upper bounds in Aschbacher–Smith,
B.5.6, printed p.105, in the deduction on printed p.928 (13.6.10).
-/

@[expose] public section

open Subgroup
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
omit [FiniteDimensional (ZMod 2) V] in
private lemma binary_twice (v : V) : v + v = 0 := by
  have h := @two_smul (ZMod 2) V _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm
/-- An order-three subgroup in a faithful binary action moves at least a plane. -/
theorem two_le_finrank_subspaceCommutator_of_card_three (A : Subgroup D) (hfaith : Function.Injective ρ)
    (hcard : Nat.card A = 3) : 2 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  classical
  have hne : A ≠ ⊥ := by rintro rfl; simp at hcard
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! hn
    exact hne (A.eq_bot_iff_forall.mpr hn)
  have ha3 : a ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hcard ▸ A.orderOf_dvd_natCard ha)
  obtain ⟨v, hv⟩ : ∃ v : V, ρ a v ≠ v := by
    by_contra! hn
    apply ha1
    apply hfaith
    ext v
    simpa using hn v
  let d : V := ρ a v - v
  have hd : d ≠ 0 := sub_ne_zero.mpr hv
  have he : ρ a d ≠ 0 := by
    intro he
    have hh := congrArg (ρ a⁻¹) he
    apply hd
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  have hne' : ρ a d ≠ d := by
    intro he
    have hc : ρ a (ρ a (ρ a v)) = v := by
      change (ρ a * ρ a * ρ a) v = v
      rw [← map_mul, ← map_mul, ← pow_two, ← pow_succ, ha3, map_one]
      rfl
    have htwice := binary_twice (ρ a v)
    have hvv := binary_twice v
    have he' : ρ a (ρ a v) = v := by
      dsimp [d] at he
      rw [map_sub] at he
      calc
        ρ a (ρ a v) = (ρ a v - v) + ρ a v := (sub_eq_iff_eq_add.mp he)
        _ = (ρ a v + ρ a v) - v := by abel
        _ = v := by rw [htwice, zero_sub]; exact neg_eq_of_add_eq_zero_left hvv
    rw [he'] at hc
    exact hv hc
  have hdm : d ∈ subspaceCommutator ρ ⊤ A := Submodule.subset_span ⟨a, ha, v, Submodule.mem_top, rfl⟩
  have hem : ρ a d ∈ subspaceCommutator ρ ⊤ A := by
    exact Submodule.subset_span ⟨a, ha, ρ a v, Submodule.mem_top, by simp [d]⟩
  let f : Fin 3 → subspaceCommutator ρ ⊤ A := ![0, ⟨d, hdm⟩, ⟨ρ a d, hem⟩]
  have hi : Function.Injective f := by
    intro i j hij
    have hh := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f, hd, he, hne', Ne.symm hd,
      Ne.symm he, Ne.symm hne'] at hh ⊢
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have h := Nat.card_le_card_of_injective f hi
  rw [Nat.card_fin, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  by_contra hn
  have hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 0 ∨
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = 1 := by omega
  rcases hdim with hh | hh <;> rw [hh] at h <;> norm_num at h

end Representation.BinaryOffender
