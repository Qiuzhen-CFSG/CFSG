module

public import Theory.SpecificGroups.BabyMonster.Presentation
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.NormNum

/-!
# Finite covers and image bounds for the Baby Monster presentation

A finite family containing the identity and closed under right multiplication
by the eleven canonical generators covers the presented group: generation and
the involution relations give an induction using positive words. Such a family
therefore supplies both finiteness and an upper bound. In the other direction,
the universal property identifies a verified image with the subgroup generated
by its eleven images, supplying a lower bound once the carrier is finite.

The target order and presentation are those of Breuer–Magaard–Wilson,
*Verification of the ordinary character table of the Baby Monster*, J. Algebra
534 (2019), §3.1, https://arxiv.org/abs/1902.07758. These comparison lemmas do not
assert that a finite cover or an image of the required order has been constructed.
-/

public section

namespace BabyMonster

/-- The order to be established for the fixed presentation. -/
@[expose]
def expectedOrder : ℕ :=
  2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

/-- The prime factorization has the required decimal expansion. -/
theorem expectedOrder_decimal : expectedOrder = 4154781481226426191177580544000000 := by
  norm_num [expectedOrder]

/-- The target order is positive. -/
theorem expectedOrder_pos : 0 < expectedOrder := by
  rw [expectedOrder_decimal]
  norm_num

/-- The canonical generators are their own inverses. -/
theorem generator_inv (i : Generator) : (generator i)⁻¹ = generator i :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generator_sq i)

/-- Induction by adjoining canonical generators on the right suffices, because
each canonical generator is its own inverse. -/
theorem induction_on_generator_mul {P : Carrier → Prop} (h1 : P 1)
    (hmul : ∀ x, P x → ∀ i, P (x * generator i)) (x : Carrier) : P x := by
  have hx : x ∈ Subgroup.closure (Set.range generator) := by
    rw [closure_range_generator]
    trivial
  refine Subgroup.closure_induction_right (p := fun x _ => P x) h1 ?_ ?_ hx
  · rintro x _ _ ⟨i, rfl⟩ hx
    exact hmul x hx i
  · rintro x _ _ ⟨i, rfl⟩ hx
    simpa only [generator_inv] using hmul x hx i

/-- A family containing the identity and closed under adjoining generators
covers the entire presented group. -/
theorem surjective_of_generator_closed_range {α : Type*} (f : α → Carrier)
    (h1 : 1 ∈ Set.range f)
    (hmul : ∀ a i, f a * generator i ∈ Set.range f) : Function.Surjective f := by
  intro x
  apply induction_on_generator_mul (P := fun x => x ∈ Set.range f) h1 _ x
  rintro _ ⟨a, rfl⟩ i
  exact hmul a i

/-- A finite family of normal forms closed under adjoining generators proves
finiteness and an upper bound. No uniqueness of normal forms is required. -/
theorem finite_and_card_le_of_generator_closed_range {α : Type*} [Finite α]
    (f : α → Carrier) (h1 : 1 ∈ Set.range f)
    (hmul : ∀ a i, f a * generator i ∈ Set.range f)
    (hcard : Nat.card α ≤ expectedOrder) :
    Finite Carrier ∧ Nat.card Carrier ≤ expectedOrder := by
  have hf := surjective_of_generator_closed_range f h1 hmul
  exact ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans hcard⟩

/-- The image of a family satisfying the relators is exactly its generated subgroup. -/
theorem range_lift {G : Type*} [Group G] {t : Generator → G} (h : Relations t) :
    (lift h).range = Subgroup.closure (Set.range t) := by
  rw [MonoidHom.range_eq_map, ← closure_range_generator, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (lift_generator h i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨generator i, ⟨i, rfl⟩, lift_generator h i⟩

/-- Once the presentation is known finite, any verified image supplies a lower
bound for its order. Finiteness of an image alone does not imply this premise. -/
theorem card_generated_le [Finite Carrier] {G : Type*} [Group G]
    {t : Generator → G} (h : Relations t) :
    Nat.card (Subgroup.closure (Set.range t)) ≤ Nat.card Carrier := by
  rw [← range_lift h]
  exact Nat.card_le_card_of_surjective (lift h).rangeRestrict
    (lift h).rangeRestrict_surjective

end BabyMonster
