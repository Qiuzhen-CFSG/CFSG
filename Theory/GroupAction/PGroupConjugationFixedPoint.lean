module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Fixed points in a set stable under p-group conjugation

If a p-group A acts by conjugation on a finite set whose cardinality is
prime to p, one element centralizes all of A. The proof builds the literal
conjugation action and applies the fixed-point congruence.

Application: a cubic subgroup centralizes some element of the 640-element
set of outer involutions in Aschbacher–Smith, J.2.6, printed p.435.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A stable set of cardinality prime to p meets the centralizer of a p-group. -/
theorem exists_mem_centralizer_of_conjugation_stable_set
    {p : ℕ} [Fact p.Prime] (A : Subgroup G) (hA : IsPGroup p A)
    (X : Set G) (hX : ∀ a : A, ∀ x ∈ X, (a : G) * x * (a : G)⁻¹ ∈ X)
    (hcard : ¬ p ∣ Nat.card X) : ∃ x ∈ X, x ∈ centralizer (A : Set G) := by
  let : MulAction A X := {
    smul a x := ⟨(a : G) * x * (a : G)⁻¹, hX a x x.property⟩
    one_smul x := Subtype.ext (by
      change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
      simp)
    mul_smul a b x := Subtype.ext (by
      change ((a : G) * b) * x * ((a : G) * b)⁻¹ =
        (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
      group) }
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card X hcard
  refine ⟨x, x.property, ?_⟩
  intro a ha
  have he := congrArg Subtype.val (hx (⟨a, ha⟩ : A))
  change a * (x : G) * a⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

end Subgroup
