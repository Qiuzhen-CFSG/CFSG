module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normalizers of subgroups of finite cyclic groups

A subgroup of order n in a finite cyclic group is exactly the kernel of
raising to the n-th power: the cyclic root bound gives equality of orders.
Conjugation preserves this power condition, so an ambient normalizer of
a cyclic subgroup normalizes every subgroup of it.

The source application is GLS4, Chapter 2, equation (12H): the two-point
stabilizer and its swapping involution preserve the prime torus line.
-/

namespace Subgroup

/-- In a finite cyclic group, the subgroup of order n contains every n-th root of one. -/
public theorem mem_of_pow_card_eq_one_in_cyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (H : Subgroup G) {x : G} (hx : x ^ Nat.card H = 1) : x ∈ H := by
  classical
  let : CommGroup G := IsCyclic.commGroup
  let : Fintype G := Fintype.ofFinite G
  let Q : Subgroup G := (powMonoidHom (Nat.card H)).ker
  have hHQ : H ≤ Q := by
    intro a ha
    change a ^ Nat.card H = 1
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : H)))
  have hcard : Nat.card Q ≤ Nat.card H := by
    simpa [Nat.card_eq_fintype_card, Q, Fintype.card_subtype,
      MonoidHom.mem_ker, powMonoidHom_apply] using
      (IsCyclic.card_pow_eq_one_le (α := G) (Nat.card_pos (α := H)))
  rw [eq_of_le_of_card_ge hHQ hcard]
  exact hx

/-- The normalizer of a finite cyclic subgroup preserves each of its subgroups. -/
public theorem normalizer_le_normalizer_of_le_cyclic {G : Type*} [Group G] [Finite G]
    (A K : Subgroup G) [IsCyclic K] (hAK : A ≤ K) :
    normalizer (K : Set G) ≤ normalizer (A : Set G) := by
  have hconj : ∀ g ∈ normalizer (K : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    let b : K := ⟨g * a * g⁻¹, (mem_normalizer_iff.mp hg a).mp (hAK ha)⟩
    apply mem_of_pow_card_eq_one_in_cyclic (A.subgroupOf K) (x := b)
    apply Subtype.ext
    change (g * a * g⁻¹) ^ Nat.card (A.subgroupOf K) = 1
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, ← MulAut.conj_apply, ← map_pow]
    rw [show a ^ Nat.card A = 1 from
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A))), map_one]
  intro g hg
  rw [mem_normalizer_iff]
  intro a
  constructor
  · exact hconj g hg a
  · intro ha
    have hh := hconj g⁻¹ ((normalizer (K : Set G)).inv_mem hg) _ ha
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one] using hh

end Subgroup
