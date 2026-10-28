module
public import Theory.GroupTheory.CyclicExtension
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Collection and normalization steps for the five-local words

A cyclic collection step allows the new generator's bounded power to lie
in the old subgroup. This handles the quaternion relation `s² = r²`.
For a finite group, conjugation carrying generators into their closure
already normalizes that closure, by equality of finite cardinalities.
These elementary helpers extend the method in `Theory.GroupTheory.CyclicExtension`.
-/

namespace Tits.FiveFrobenius
open Subgroup

/-- A collection step allowing a nontrivial power in the old subgroup. -/
public theorem collect_power_mem
    {G : Type*} [Group G] [Finite G]
    (S : Set G) (a : G) (m : ℕ) (hm : 0 < m) (ha : a ^ m ∈ closure S)
    (hc : ∀ b ∈ S, a * b * a⁻¹ ∈ closure S)
    {x : G} (hx : x ∈ closure (insert a S)) :
    ∃ y ∈ closure S, ∃ i : Fin m, y * a ^ i.val = x := by
  have hconj : ∀ y ∈ closure S, a * y * a⁻¹ ∈ closure S := by
    have hle : closure S ≤ (closure S).comap (MulAut.conj a).toMonoidHom :=
      (closure_le _).mpr hc
    exact hle
  change x ∈ (closure (insert a S)).toSubmonoid at hx
  rw [closure_toSubmonoid_of_finite] at hx
  induction hx using Submonoid.closure_induction_left with
  | one => exact ⟨1, (closure S).one_mem, ⟨0, hm⟩, by simp⟩
  | mul_left b hb x _ ih =>
    rcases ih with ⟨y, hy, i, rfl⟩
    rcases hb with rfl | hb
    · refine ⟨(b * y * b⁻¹) * (b ^ m) ^ ((i.val + 1) / m),
        mul_mem (hconj y hy) (pow_mem ha _),
        ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩, ?_⟩
      rw [mul_assoc, ← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [pow_succ']
      simp [mul_assoc]
    · exact ⟨b * y, mul_mem (subset_closure hb) hy, i, mul_assoc _ _ _⟩

public theorem normalizes_closure
    {G : Type*} [Group G] [Finite G] (S : Set G) (a : G)
    (hc : ∀ b ∈ S, a * b * a⁻¹ ∈ closure S) :
    a ∈ normalizer (closure S : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact hc b hb
  · rw [card_map_of_injective (MulAut.conj a).injective]

end Tits.FiveFrobenius
