module

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Cubic lifts under an involutive inverter

Suppose an involution centralizes the kernel of a homomorphism and inverts
the image of a normal subgroup, with that image having exponent three. Every element of that
image has a lift of exponent dividing three in the subgroup. No finiteness
or condition on the kernel's prime divisors is required.

For a lift y, the commutator x = w y w⁻¹ y⁻¹ has the same image as y.
The inverter inverts x, whereas it fixes x³ because that cube is in the
kernel. Thus x⁶ = 1, and x⁴ is the required cubic lift.

Source application: Aschbacher–Smith, Lemma 15.3.7, printed p.1122.
-/

namespace Subgroup

/-- An involutive inverter centralizing the kernel supplies cubic lifts. -/
public theorem exists_cubic_lift_of_involutive_inverter {H K : Type*} [Group H] [Group K]
    (f : H →* K) (P : Subgroup H) [P.Normal]
    (w : H) (hw : w ^ 2 = 1)
    (hc : ∀ k ∈ f.ker, w * k = k * w)
    (hi : ∀ y ∈ P, f (w * y * w⁻¹) = (f y)⁻¹)
    (he : ∀ y ∈ P, (f y) ^ 3 = 1)
    (y : H) (hy : y ∈ P) : ∃ z ∈ P, z ^ 3 = 1 ∧ f z = f y := by
  let x := w * y * w⁻¹ * y⁻¹
  have hxP : x ∈ P := P.mul_mem (Subgroup.Normal.conj_mem inferInstance y hy w) (P.inv_mem hy)
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hix : w * x * w⁻¹ = x⁻¹ := by
    dsimp [x]
    simp only [mul_inv_rev, inv_inv, hwi, ← mul_assoc,
      show w * w = 1 by simpa only [pow_two] using hw, one_mul]
  have hfx : f x = f y := by
    dsimp [x]
    rw [map_mul, hi y hy, map_inv, ← mul_inv_rev, ← pow_two]
    have hp := he y hy
    have hh : (f y) ^ 2 * f y = 1 := by simpa only [pow_succ] using hp
    exact inv_eq_of_mul_eq_one_right hh
  have hx3 : x ^ 3 ∈ f.ker := by
    change f (x ^ 3) = 1
    rw [map_pow, hfx, he y hy]
  have hfix : w * (x ^ 3) * w⁻¹ = x ^ 3 := by
    rw [hc _ hx3, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : w * (x ^ 3) * w⁻¹ = (x ^ 3)⁻¹ := by
    change MulAut.conj w (x ^ 3) = (x ^ 3)⁻¹
    rw [map_pow]
    change (w * x * w⁻¹) ^ 3 = _
    rw [hix, inv_pow]
  have hx6 : x ^ 6 = 1 := by
    calc
      x ^ 6 = x ^ 3 * x ^ 3 := by rw [← pow_add]
      _ = x ^ 3 * (x ^ 3)⁻¹ := congrArg (x ^ 3 * ·) (hfix.symm.trans hinv)
      _ = 1 := mul_inv_cancel _
  refine ⟨x ^ 4, P.pow_mem hxP _, ?_, ?_⟩
  · rw [← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, hx6, one_pow]
  · rw [map_pow, hfx, show 4 = 3 + 1 from rfl, pow_add, he y hy, one_mul, pow_one]
end Subgroup
