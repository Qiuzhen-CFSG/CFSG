module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Coordinates for the twelfth-cyclotomic triality torus

The composition of the D4 diagram/Frobenius with the central and first-arm
reflections fixes the tuple `(z, z^(q³+1), z^q, z^(q²))` when
`z^(q⁴-q²+1) = 1`. Projection onto the first coordinate is injective.
Over an algebraically closed field of characteristic two these parameters
form a cyclic group of order `q⁴-q²+1`.

`SpinTorus` realizes these coordinates by actual simple-coroot words. This
scalar calculation alone makes no assertion about a finite triality carrier.
Source: GLS3 §§1.12, 2.2; the multiplier application is §6.1, Theorem 6.1.4.
-/

@[expose] public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve

/-- The twelfth cyclotomic factor, using natural subtraction. -/
def order (q : ℕ) : ℕ := q ^ 4 - q ^ 2 + 1

lemma order_pos (q : ℕ) : 0 < order q := by unfold order; omega

/-- The one-parameter solution in the four numbered simple-coroot coordinates. -/
def expand {A : Type*} [CommGroup A] (q : ℕ) : A →* (Fin 4 → A) where
  toFun z := ![z, z ^ (q ^ 3 + 1), z ^ q, z ^ (q ^ 2)]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' x y := by ext i; fin_cases i <;> simp [mul_pow]

/-- Coordinate action of first-arm reflection after central reflection after graph-field. -/
def twist {A : Type*} [CommGroup A] (q : ℕ) (t : Fin 4 → A) : Fin 4 → A :=
  ![((t 0 * t 2) / t 1) ^ q, ((t 0 * t 2 * t 3) / t 1) ^ q, t 0 ^ q, t 2 ^ q]

lemma expand_injective {A : Type*} [CommGroup A] (q : ℕ) :
    Function.Injective (expand (A := A) q) := by
  intro x y h
  exact congrFun h 0

lemma expand_fixed {A : Type*} [CommGroup A] {q : ℕ} (_hq : 1 ≤ q)
    (z : A) (hz : z ^ order q = 1) : twist q (expand q z) = expand q z := by
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have he : order q + q ^ 2 = q ^ 4 + 1 := by unfold order; omega
  have hz' : z ^ (q ^ 4 + 1) = z ^ (q ^ 2) := by
    rw [← he, pow_add, hz, one_mul]
  have h0 : ((z * z ^ q) / z ^ (q ^ 3 + 1)) ^ q = z := by
    rw [div_pow, div_eq_iff_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    calc
      z ^ q * z ^ (q * q) = z ^ q * z ^ (q ^ 4 + 1) := by rw [hz', pow_two]
      _ = z * z ^ ((q ^ 3 + 1) * q) := by
        simp only [← pow_add, ← pow_succ']; congr 1; ring
  ext i
  fin_cases i
  · exact h0
  · change ((z * z ^ q * z ^ (q ^ 2)) / z ^ (q ^ 3 + 1)) ^ q = z ^ (q ^ 3 + 1)
    rw [show (z * z ^ q * z ^ (q ^ 2)) / z ^ (q ^ 3 + 1) =
      ((z * z ^ q) / z ^ (q ^ 3 + 1)) * z ^ (q ^ 2) by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm],
      mul_pow, h0, ← pow_mul]
    simp [pow_succ', mul_assoc]
  · rfl
  · change (z ^ q) ^ q = z ^ (q ^ 2)
    rw [← pow_mul, pow_two]


instance orderNeZero (q : ℕ) : NeZero (order q) := ⟨(order_pos q).ne'⟩

/-- The scalar parameter group used by the concrete coroot construction. -/
abbrev Parameters (k : Type*) [CommRing k] (n : ℕ) := rootsOfUnity (order (2 ^ n)) k

variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

omit [IsAlgClosed k] in
/-- The torus order is prime to the characteristic. -/
theorem order_cast (n : ℕ) (hn : 0 < n) : (order (2 ^ n) : k) = 1 := by
  have hq4 : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ 4 := by
    nlinarith [sq_nonneg ((2 ^ n) * (2 ^ n) - 1 : ℤ)]
  have htwo : (2 : k) = 0 := by simpa using (CharP.cast_eq_zero k 2)
  simp [order, Nat.cast_sub hq4, htwo, hn.ne']

/-- All roots of the prime-to-characteristic torus polynomial occur. -/
theorem card_parameters (n : ℕ) (hn : 0 < n) :
    Nat.card (Parameters k n) = order (2 ^ n) := by
  let : NeZero (order (2 ^ n) : k) := ⟨by rw [order_cast k n hn]; exact one_ne_zero⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity k _

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
