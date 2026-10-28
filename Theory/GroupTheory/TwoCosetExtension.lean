module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

/-!
# Adjoining one binary coset to a subgroup

If `a²` belongs to `K` and conjugation by `a⁻¹` carries `K` into itself,
then `K ∪ aK` is a subgroup. Its order is at most twice the order of `K`.
The proof writes out multiplication and inversion in the two cosets and
uses the explicit surjection from `Bool × K` for the cardinal bound.
This is the elementary collection step for triangular binary presentations.
-/

@[expose] public section
namespace Subgroup

variable {G : Type*} [Group G]

/-- The subgroup consisting of `K` and its left coset `aK`. -/
def twoCosetExtension (K : Subgroup G) (a : G) (hs : a * a ∈ K)
    (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) : Subgroup G where
  carrier := {g | g ∈ K ∨ ∃ k ∈ K, g = a * k}
  one_mem' := Or.inl K.one_mem
  mul_mem' := by
    intro g h hg hh
    rcases hg with hg | ⟨k, hk, rfl⟩ <;> rcases hh with hh | ⟨l, hl, rfl⟩
    · exact Or.inl (K.mul_mem hg hh)
    · refine Or.inr ⟨a⁻¹ * g * a * l, K.mul_mem (hc g hg) hl, ?_⟩
      group
    · exact Or.inr ⟨k * h, K.mul_mem hk hh, mul_assoc _ _ _⟩
    · apply Or.inl
      have he : a * k * (a * l) = (a * a) * (a⁻¹ * k * a) * l := by group
      rw [he]
      exact K.mul_mem (K.mul_mem hs (hc k hk)) hl
  inv_mem' := by
    intro g hg
    rcases hg with hg | ⟨k, hk, rfl⟩
    · exact Or.inl (K.inv_mem hg)
    · refine Or.inr ⟨(a⁻¹ * k⁻¹ * a) * (a * a)⁻¹,
        K.mul_mem (hc k⁻¹ (K.inv_mem hk)) (K.inv_mem hs), ?_⟩
      group

/-- The two chosen cosets cover the extension, allowing them to coincide. -/
def twoCosetExtensionCover (K : Subgroup G) (a : G) (hs : a * a ∈ K)
    (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) : Bool × K → twoCosetExtension K a hs hc :=
  fun p => if p.1 then ⟨a * p.2, Or.inr ⟨p.2, p.2.property, rfl⟩⟩
    else ⟨p.2, Or.inl p.2.property⟩

theorem twoCosetExtensionCover_surjective (K : Subgroup G) (a : G) (hs : a * a ∈ K)
    (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) : Function.Surjective (twoCosetExtensionCover K a hs hc) := by
  intro ⟨g, hg⟩
  rcases hg with hg | ⟨k, hk, rfl⟩
  · exact ⟨(false, ⟨g, hg⟩), rfl⟩
  · exact ⟨(true, ⟨k, hk⟩), rfl⟩

instance twoCosetExtension_finite (K : Subgroup G) [Finite K] (a : G) (hs : a * a ∈ K)
    (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) : Finite (twoCosetExtension K a hs hc) :=
  Finite.of_surjective _ (twoCosetExtensionCover_surjective K a hs hc)

theorem twoCosetExtension_card (K : Subgroup G) [Finite K] (a : G) (hs : a * a ∈ K)
    (hc : ∀ k ∈ K, a⁻¹ * k * a ∈ K) :
    Nat.card (twoCosetExtension K a hs hc) ≤ 2 * Nat.card K := by
  have h := Nat.card_le_card_of_surjective _ (twoCosetExtensionCover_surjective K a hs hc)
  simpa using h

end Subgroup
