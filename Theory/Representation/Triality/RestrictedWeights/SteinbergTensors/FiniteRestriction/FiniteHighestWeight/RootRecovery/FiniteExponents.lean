module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The two endpoints in finite diagonal-character separation

Equality of powers on the units of a finite field distinguishes degrees in
`[0, |F|)` once one also knows whether the degree is zero. This uses a generator
of the cyclic unit group and keeps `0` and `|F|-1` as separate cases, including
`|F| = 2`. The independent rational SL2 argument must supply that endpoint
test using a genuine root or Weyl action.

This is the arithmetic step of GLS3 2.8.2 / Steinberg §13.3(a), in the same
form used by `Theory.Representation.SL2.HighestWeightUnique`.
-/

public section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery

/-- In the full restricted interval, finite diagonal characters separate
exponents once the zero endpoint is distinguished. In particular this retains
both endpoints when the field has two elements. -/
theorem restricted_nat_exponents_eq {F : Type*} [Field F] [Finite F]
    {m l : ℕ} (hm : m < Nat.card F) (hl : l < Nat.card F)
    (hzero : m = 0 ↔ l = 0) (hpow : ∀ a : Fˣ, a ^ m = a ^ l) : m = l := by
  by_cases hm0 : m = 0
  · exact hm0.trans (hzero.mp hm0).symm
  have hl0 : l ≠ 0 := fun h => hm0 (hzero.mpr h)
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ho : orderOf a = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  have heq : a ^ (m-1) = a ^ (l-1) := by
    apply mul_right_cancel (b := a)
    simpa only [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m),
      Nat.sub_add_cancel (by omega : 1 ≤ l)] using hpow a
  have hml := pow_injOn_Iio_orderOf (x := a)
    (show m-1 < orderOf a by rw [ho]; omega)
    (show l-1 < orderOf a by rw [ho]; omega) heq
  omega

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
