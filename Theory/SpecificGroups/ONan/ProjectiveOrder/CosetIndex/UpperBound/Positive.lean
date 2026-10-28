module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.Bounds
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Recovering inverse transitions from positive O'Nan coset transitions

The concrete matrix model is finite independently of its order. Each generator
therefore has a positive power equal to one. Repeated positive transitions give
an actual equality for multiplication by its inverse. This halves the numerical
transition obligations without assuming any permutation table is faithful.
-/

namespace ONan.OrderCertificate.UpperBound

private theorem positive_power (repr : Fin 122760 → Model)
    (step : ∀ i a, ∃ h : localSubgroup, ∃ j,
      repr i * cosetGenerators a = h.val * repr j)
    (a : Bool) (n : Nat) (i : Fin 122760) :
    ∃ h : localSubgroup, ∃ j, repr i * cosetGenerators a ^ n = h.val * repr j := by
  induction n generalizing i with
  | zero => exact ⟨1, i, by simp⟩
  | succ n ih =>
    obtain ⟨h, j, hj⟩ := ih i
    obtain ⟨k, l, hl⟩ := step j a
    refine ⟨h * k, l, ?_⟩
    change repr i * cosetGenerators a ^ (n + 1) = (h.val * k.val) * repr l
    rw [pow_succ, ← mul_assoc, hj, mul_assoc, hl, ← mul_assoc]

/-- Positive transitions alone suffice in the fixed finite model.
The inverse transitions are proved as equalities with factors in the same
word-generated subgroup, rather than inferred from an external action. -/
public def coverOfPositive (repr : Fin 122760 → Model) (initial : Fin 122760)
    (hroot : repr initial = 1)
    (step : ∀ i a, ∃ h : localSubgroup, ∃ j,
      repr i * cosetGenerators a = h.val * repr j) :
    Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 122760) where
  repr := repr
  initial := initial
  initial_eq := hroot
  step := step
  inv_step i a := by
    obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite (cosetGenerators a)).exists_pow_eq_one
    have hp : cosetGenerators a ^ (n - 1) = (cosetGenerators a)⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← pow_succ, Nat.sub_add_cancel hn, he]
    simpa only [hp] using positive_power repr step a (n - 1) i

end ONan.OrderCertificate.UpperBound
