module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.Arithmetic

/-!
# Separation of packed columns

A natural number below `5^133` is uniquely determined by its 133 base-five
digits. Thus distinct bounded packed values give distinct columns. This lets
an orbit certificate separate its columns by integer comparisons, independently
of its tree of generator steps.

The proof is the usual uniqueness of radix expansion, by quotient and remainder.
The encoding convention is documented in `source/README.md`.
-/

namespace HaradaNorton.OrderCertificate.IndexArithmetic

private theorem eq_of_digits_eq (n x y : ℕ) (hx : x < 5 ^ n) (hy : y < 5 ^ n)
    (h : ∀ j < n, x / 5 ^ j % 5 = y / 5 ^ j % 5) : x = y := by
  induction n generalizing x y with
  | zero => simp only [pow_zero] at hx hy; omega
  | succ n ih =>
    have hx' : x / 5 < 5 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hx)
    have hy' : y / 5 < 5 ^ n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
      simpa only [pow_succ] using hy)
    have hq : x / 5 = y / 5 := ih (x / 5) (y / 5) hx' hy' (by
      intro j hj
      simpa only [Nat.div_div_eq_div_mul, pow_succ'] using h (j + 1) (by omega))
    have hr : x % 5 = y % 5 := by simpa using h 0 (by omega)
    omega

/-- Bounded packed values with identical decoded columns are equal. -/
public theorem eq_of_decodeVector_eq {x y : ℕ} (hx : x < 5 ^ 133) (hy : y < 5 ^ 133)
    (h : decodeVector x = decodeVector y) : x = y := by
  apply eq_of_digits_eq 133 x y hx hy
  intro j hj
  have hd := congrArg ZMod.val (congrFun h (⟨j, hj⟩ : Fin 133))
  simpa only [decodeVector, ZMod.val_natCast, Nat.mod_mod] using hd

/-- An injective enumeration of bounded packed integers separates its columns. -/
public theorem decodeVector_injective_on_family {ι : Type*} (packed : ι → ℕ)
    (hbound : ∀ i, packed i < 5 ^ 133) (hinj : Function.Injective packed) :
    Function.Injective (fun i => decodeVector (packed i)) := by
  intro i j hij
  exact hinj (eq_of_decodeVector_eq (hbound i) (hbound j) hij)

end HaradaNorton.OrderCertificate.IndexArithmetic
