module
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Integer data for the first large-ratio decomposition

The three entries refer to X₂, Z₁, Z₂. Degrees and exceptional multiplicities
are signed; the involution values use those same signs. The two column sums
come from the actual exceptional Gram matrix. The Suzuki equation is written
without denominators. These are necessary arithmetic constraints, with no
assertion about the final order built into the data.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.CaseOneLarge
open scoped BigOperators

/-- Involution values in signed rows (1,0,1,a,b), (0,0,1,a,b), (0,0,1,a,b). -/
@[expose] public def tripleValue (a b : Fin 3 → ℤ) (j : Fin 3) : ℤ :=
  (if j = 0 then 8 else 1) + 8 * a j + 3 * b j

/-- Numerator of the third Suzuki sum after clearing the three degrees. -/
@[expose] public def suzukiNumerator (d t : Fin 3 → ℤ) : ℤ :=
  d 0 * d 1 * d 2 + t 0 ^ 2 * d 1 * d 2 +
    t 1 ^ 2 * d 0 * d 2 + t 2 ^ 2 * d 0 * d 1

/-- Necessary integer constraints, to be discharged by the arithmetic exhaustion. -/
public structure LargeCaseData (g : ℤ) where
  degree : Fin 3 → ℤ
  fourth : Fin 3 → ℤ
  fifth : Fin 3 → ℤ
  fourth_bounds : ∀ j, -1 ≤ fourth j ∧ fourth j ≤ 1
  fifth_bounds : ∀ j, -1 ≤ fifth j ∧ fifth j ≤ 1
  fourth_sum : ∑ j, fourth j = 1
  fifth_sum : ∑ j, fifth j = -1
  degree_ne_zero : ∀ j, degree j ≠ 0
  degree_sum : ∑ j, degree j = -1
  degree_dvd : ∀ j, degree j ∣ g
  degree_congruence : ∀ j, (128 : ℤ) ∣ degree j +
    (if j = 0 then 280 else 127) + 280 * fourth j + 45 * fifth j
  large : ∃ j, (degree j).natAbs < 4 * (tripleValue fourth fifth j).natAbs ^ 2
  suzuki : g * suzukiNumerator degree (tripleValue fourth fifth) =
    1118208 * degree 0 * degree 1 * degree 2

/-- Divisibility of two degrees bounds the denominator once the third is fixed.
The elementary identity yz | g(y+z) avoids any coprimality assumption. -/
public theorem numerator_dvd_fixed (g x y z t u v : ℤ)
    (hy : y ≠ 0) (hz : z ≠ 0) (hyG : y ∣ g) (hzG : z ∣ g)
    (hs : x + y + z = -1)
    (he : g * (x*y*z+t^2*y*z+u^2*x*z+v^2*x*y) = 1118208*x*y*z) :
    (x*y*z+t^2*y*z+u^2*x*z+v^2*x*y) ∣ 1118208*x*(1+x) := by
  obtain ⟨a, ha⟩ := hyG
  obtain ⟨b, hb⟩ := hzG
  have hsum : g * (1+x) = y*z*(-(a+b)) := by
    calc
      g * (1+x) = -(g*z+g*y) := by
        have hx : 1+x = -(y+z) := by linarith
        rw [hx]; ring
      _ = y*z*(-(a+b)) := by
        nlinarith [congrArg (fun w => w*z) ha, congrArg (fun w => w*y) hb]
  refine ⟨-(a+b), ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hy hz)
  calc
    y*z*(1118208*x*(1+x)) = (1+x)*(1118208*x*y*z) := by ring
    _ = (1+x)*(g*(x*y*z+t^2*y*z+u^2*x*z+v^2*x*y)) := by rw [he]
    _ = (g*(1+x))*(x*y*z+t^2*y*z+u^2*x*z+v^2*x*y) := by ring
    _ = y*z*((x*y*z+t^2*y*z+u^2*x*z+v^2*x*y)*(-(a+b))) := by rw [hsum]; ring

/-- A checked numerical upper bound on a quadratic confines the other degree.
All inequalities are integer inequalities; no square-root approximation is used. -/
public theorem abs_lt_of_quadratic_dvd (A B C M y N : ℤ)
    (_hN : 0 ≤ N) (hB : |B| < |A| * N)
    (hbound : |A| * N^2 > |B| * N + |C| + |M|)
    (hM : M ≠ 0) (hd : (A*y^2+B*y+C) ∣ M) : |y| < N := by
  have hdabs : |A*y^2+B*y+C| ≤ |M| := Int.le_of_dvd (abs_pos.mpr hM)
    ((abs_dvd_abs _ _).mpr hd)
  have ht : |A| * y^2 ≤ |M| + |B| * |y| + |C| := by
    calc
      |A| * y^2 = |A*y^2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
      _ = |(A*y^2+B*y+C) - (B*y+C)| := by congr 1; ring
      _ ≤ |A*y^2+B*y+C| + |B*y+C| := abs_sub _ _
      _ ≤ |M| + (|B*y| + |C|) := add_le_add hdabs (abs_add_le _ _)
      _ = |M| + |B| * |y| + |C| := by rw [abs_mul]; ring
  by_contra hn
  have hy : N ≤ |y| := le_of_not_gt hn
  have hp : 0 ≤ (|y|-N) * (|A| *(|y|+N)-|B|) := by
    apply mul_nonneg (sub_nonneg.mpr hy)
    have := mul_nonneg (abs_nonneg A) (abs_nonneg y)
    nlinarith
  rw [← sq_abs y] at ht
  nlinarith

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.CaseOneLarge
