module

public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Choose.Dvd

/-!
# First omega in odd-prime groups of class two

In a group with central commutators, the product of two p-th roots of one
is again a p-th root of one when p is odd. The collection formula has a
commutator factor with exponent `p.choose 2`, which is divisible by p.
Thus the first omega subgroup has exponent dividing p, including when it
is trivial. Applied inside the second center, this supplies a characteristic
subgroup of exponent dividing p for the supercritical construction.

Source: Aschbacher, *Finite Group Theory*, (23.11), printed p.110.
The private collection identities are adapted from this repository's
`Theory.GroupTheory.PGroup.OddOmegaAutomorphisms`.
-/

open Subgroup
open scoped commutatorElement

private theorem supercritical_pow_mul_swap_of_relation
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_y : Commute c y) :
    ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        y ^ (n + 1) * x = y * (y ^ n * x) := by simp [pow_succ', mul_assoc]
        _ = y * (c ^ n * x * y ^ n) := by
              rw [supercritical_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = y * c ^ n * x * y ^ n := by simp [mul_assoc]
        _ = c ^ n * y * x * y ^ n := by
              have hycn : Commute (c ^ n) y := hc_y.pow_left n
              rw [hycn.eq]
        _ = c ^ n * (y * x) * y ^ n := by simp [mul_assoc]
        _ = c ^ n * (c * x * y) * y ^ n := by rw [hrel]
        _ = (c ^ n * c) * x * (y * y ^ n) := by simp [mul_assoc]
        _ = (c ^ n * c) * x * (y ^ n * y) := by
              have hy_pow_comm : y * y ^ n = y ^ n * y := by
                calc
                  y * y ^ n = y ^ (n + 1) := (pow_succ' y n).symm
                  _ = y ^ n * y := pow_succ y n
              rw [hy_pow_comm]
        _ = c ^ (n + 1) * x * y ^ (n + 1) := by
              simp [pow_succ, mul_assoc]

private theorem supercritical_pow_mul_eq_cpow_mul_pow_mul_pow
    {M : Type*} [Group M] (x y c : M)
    (hrel : y * x = c * x * y)
    (hc_x : Commute c x)
    (hc_y : Commute c y) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (Nat.choose n 2) * x ^ n * y ^ n
  | 0 => by simp
  | n + 1 => by
      calc
        (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := by simp [pow_succ]
        _ = (c ^ (Nat.choose n 2) * x ^ n * y ^ n) * (x * y) := by
              rw [supercritical_pow_mul_eq_cpow_mul_pow_mul_pow x y c hrel hc_x hc_y n]
        _ = c ^ (Nat.choose n 2) * x ^ n * (y ^ n * x) * y := by simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * x ^ n * (c ^ n * x * y ^ n) * y := by
              rw [supercritical_pow_mul_swap_of_relation x y c hrel hc_y n]
        _ = c ^ (Nat.choose n 2) * (x ^ n * c ^ n) * x * y ^ n * y := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose n 2) * (c ^ n * x ^ n) * x * y ^ n * y := by
              have hcxnn : Commute (c ^ n) (x ^ n) := (hc_x.pow_left n).pow_right n
              rw [hcxnn.symm.eq]
        _ = (c ^ (Nat.choose n 2) * c ^ n) * (x ^ n * x) * (y ^ n * y) := by
              simp [mul_assoc]
        _ = c ^ (Nat.choose (n + 1) 2) * x ^ (n + 1) * y ^ (n + 1) := by
              have hchoose : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
                simpa [Nat.choose_one_right, Nat.add_comm] using
                  (Nat.choose_succ_right (n := n + 1) (k := 1) (Nat.succ_pos n))
              rw [hchoose, pow_add, pow_succ, pow_succ]

private theorem supercritical_prime_dvd_choose_two {p : ℕ} [Fact (Nat.Prime p)]
    (hpodd : p ≠ 2) :
    p ∣ Nat.choose p 2 := by
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hpodd)
  exact Nat.Prime.dvd_choose_self (Fact.out : Nat.Prime p) (k := 2) (by decide) hlt

private theorem supercritical_choose_two_pow_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {M : Type*} [Group M] {c : M}
    (hpodd : p ≠ 2) (hc : c ^ p = 1) :
    c ^ Nat.choose p 2 = 1 := by
  rcases supercritical_prime_dvd_choose_two (p := p) hpodd with ⟨k, hk⟩
  calc
    c ^ Nat.choose p 2 = c ^ (p * k) := by simp [hk]
    _ = (c ^ p) ^ k := by rw [pow_mul]
    _ = 1 := by simp [hc]


/-- In class at most two, odd-prime roots of one are closed under multiplication. -/
public theorem mul_pow_eq_one_of_class_two
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hclass : _root_.commutator G ≤ center G) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : (x * y) ^ p = 1 := by
  have hm : ⁅y, x⁆ ∈ center G :=
    hclass (commutator_mem_commutator (mem_top _) (mem_top _))
  have hrel : y * x = ⁅y, x⁆ * x * y := by
    simp [commutatorElement_def, mul_assoc]
  have hcx : Commute ⁅y, x⁆ x := ((mem_center_iff.mp hm) x).symm
  have hcy : Commute ⁅y, x⁆ y := ((mem_center_iff.mp hm) y).symm
  have hcp : ⁅y, x⁆ ^ p = 1 := by
    have he := supercritical_pow_mul_swap_of_relation x y ⁅y, x⁆ hrel hcy p
    rw [hy, one_mul, mul_one] at he
    exact (mul_right_cancel (he.symm.trans (one_mul x).symm))
  rw [supercritical_pow_mul_eq_cpow_mul_pow_mul_pow x y ⁅y, x⁆ hrel hcx hcy,
    supercritical_choose_two_pow_eq_one hp hcp, hx, hy, one_mul, one_mul]

/-- The first omega subgroup of an odd-prime class-two group has exponent dividing p. -/
public theorem exponent_omega_one_dvd_of_class_two
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hclass : _root_.commutator G ≤ center G) :
    Monoid.exponent (omega₁ G (p := p)) ∣ p := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  exact closure_induction (p := fun z _ => z ^ p = 1)
    (fun y hy => by
      change y ^ (p ^ 1) = 1 at hy
      simpa only [pow_one] using hy) (one_pow p)
    (fun y z _ _ hy hz => mul_pow_eq_one_of_class_two hp hclass hy hz)
    (fun y _ hy => by rw [inv_pow, hy, inv_one]) x.property

/-- The second center has nilpotency class at most two. -/
public theorem commutator_second_center_le_center {G : Type*} [Group G] :
    _root_.commutator (Subgroup.upperCentralSeries G 2) ≤ center (Subgroup.upperCentralSeries G 2) := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  have hm : (⁅(x : G), (y : G)⁆) ∈ center G := by
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.mem_upperCentralSeries_succ_iff.mp x.property (y : G))
  apply mem_center_iff.mpr
  intro z
  exact Subtype.ext (mem_center_iff.mp hm z)

/-- First omega in the second center has exponent dividing an odd prime. -/
public theorem exponent_omega_one_second_center_dvd
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Monoid.exponent (omega₁ (Subgroup.upperCentralSeries G 2) (p := p)) ∣ p :=
  exponent_omega_one_dvd_of_class_two hp commutator_second_center_le_center
