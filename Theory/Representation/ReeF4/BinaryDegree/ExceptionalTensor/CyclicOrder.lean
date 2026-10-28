module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Ordinary Frobenius order on the exceptional factors

The exceptional tensor factors are indexed by the powers of the exceptional
endomorphism, whose square is ordinary Frobenius. For the Ree field exponent
`2*k+1`, multiplication by two permutes the index set, with inverse
multiplication by `k+1`. Reindexing by this permutation preserves the product
of the factor dimensions and turns invariance under a shift by `2*r` into
period `r` of the sequence indexed by ordinary Frobenius.

Source: GLS3, Corollary 2.8.6(b) and Remark 2.8.8. Its half-integer parameter
is `2^(k+1/2)`; the concrete Ree model uses field size `2^(2*k+1)`.
-/

public section

namespace ReeF4.BinaryDegree.ExceptionalTensor

/-- In the odd cyclic index group, `k+1` is the inverse of two. -/
theorem two_mul_half (k : ℕ) : (2 : ZMod (2 * k + 1)) * (k + 1) = 1 := by
  have hz := ZMod.natCast_self (2 * k + 1)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hz
  calc
    (2 : ZMod (2 * k + 1)) * (k + 1) = (2 * k + 1) + 1 := by ring
    _ = 1 := by rw [hz, zero_add]

/-- The exceptional index belonging to the `i`th ordinary Frobenius twist. -/
def ordinaryIndex (k : ℕ) : Equiv.Perm (ZMod (2 * k + 1)) where
  toFun i := 2 * i
  invFun i := (k + 1) * i
  left_inv i := by
    dsimp only
    rw [← mul_assoc, mul_comm (_ + 1) 2, two_mul_half, one_mul]
  right_inv i := by
    dsimp only
    rw [← mul_assoc, two_mul_half, one_mul]

@[simp] theorem ordinaryIndex_apply (k : ℕ) (i : ZMod (2 * k + 1)) :
    ordinaryIndex k i = 2 * i := by rfl

/-- A product over natural representatives is the product over the cyclic group. -/
theorem prod_range_cast (k : ℕ) {M : Type*} [CommMonoid M]
    (a : ZMod (2 * k + 1) → M) :
    (∏ i ∈ Finset.range (2 * k + 1), a (i : ZMod (2 * k + 1))) =
      ∏ i : ZMod (2 * k + 1), a i := by
  rw [← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_equiv (ZMod.finEquiv (2 * k + 1)).toEquiv _ _ (fun i => by
    congr 1
    exact ZMod.natCast_zmod_val (ZMod.finEquiv (2 * k + 1) i))

/-- Ordinary Frobenius ordering preserves the product of all factors. -/
theorem prod_ordinaryIndex (k : ℕ) {M : Type*} [CommMonoid M]
    (a : ZMod (2 * k + 1) → M) :
    (∏ i ∈ Finset.range (2 * k + 1), a (2 * (i : ZMod (2 * k + 1)))) =
      ∏ i : ZMod (2 * k + 1), a i := by
  rw [prod_range_cast k (fun i => a (2 * i))]
  exact Fintype.prod_equiv (ordinaryIndex k) _ _ (fun _ => rfl)

/-- A shift by `2*r` in exceptional indices is period `r` in ordinary order. -/
theorem periodic_of_exceptional_shift (k r : ℕ) {A : Type*}
    (a : ZMod (2 * k + 1) → A)
    (h : ∀ i, a (i + 2 * (r : ZMod (2 * k + 1))) = a i) :
    Function.Periodic (fun i : ℕ => a (2 * (i : ZMod (2 * k + 1)))) r := by
  intro i
  simpa only [Nat.cast_add, mul_add] using h (2 * (i : ZMod (2 * k + 1)))

end ReeF4.BinaryDegree.ExceptionalTensor
