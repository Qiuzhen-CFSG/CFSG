module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupAction.Quotient
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Prime-order automorphisms fixing the roots of an abelian p-group

Let an automorphism alpha of an abelian p-group have order dividing an odd
prime p and fix every p-th root of one. Then alpha(a)/a is a p-th root for
every a. Induct on a p-power annihilating a. With b = alpha(a)/a and
c = alpha(b)/b, induction gives b^(p²) = 1. Root fixation then gives
c^p = 1 and alpha(c) = c. The iteration formula
alpha^n(a) = a b^n c^(n choose 2), at n = p, gives b^p = 1.

For conjugation on a normal abelian subgroup A, this says that an element
of order dividing p centralizing first omega in A acts trivially on
A modulo that omega subgroup. This is the mathematical content of
Aschbacher, *Finite Group Theory*, Second Edition, (23.15)(3), printed
p.111; the calculation replaces its normalizer argument and does not
require A to be maximal.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

private theorem aut_pow_apply_of_two_differences
    {A : Type*} [CommGroup A] (α : MulAut A) (a b c : A)
    (ha : α a = a * b) (hb : α b = b * c) (hc : α c = c) (n : ℕ) :
    (α ^ n) a = a * b ^ n * c ^ (n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1
    calc
      (α ^ (n + 1)) a = α ((α ^ n) a) := by rw [pow_succ']; rfl
      _ = (a * b) * (b * c) ^ n * c ^ (n.choose 2) := by
        rw [ih, map_mul, map_mul, map_pow, map_pow, ha, hb, hc]
      _ = a * b ^ (n + 1) * c ^ ((n + 1).choose 2) := by
        simp only [hchoose, pow_add, pow_one, mul_pow]
        ac_rfl

private theorem aut_prime_difference_aux
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {A : Type*} [CommGroup A] (α : MulAut A) (hα : α ^ p = 1)
    (hfix : ∀ a : A, a ^ p = 1 → α a = a) :
    ∀ n : ℕ, ∀ a : A, a ^ (p ^ n) = 1 → (α a * a⁻¹) ^ p = 1 := by
  intro n
  induction n with
  | zero =>
    intro a ha
    have ha1 : a = 1 := by simpa using ha
    simp [ha1]
  | succ n ih =>
    intro a ha
    let b := α a * a⁻¹
    let c := α b * b⁻¹
    have hbpp : (b ^ p) ^ p = 1 := by
      have hh := ih (a ^ p) (by simpa only [← pow_mul, ← Nat.pow_succ'] using ha)
      simpa only [b, mul_pow, inv_pow, map_pow] using hh
    have hbpfix : α (b ^ p) = b ^ p := hfix _ hbpp
    have hcp : c ^ p = 1 := by
      dsimp [c]
      rw [mul_pow, inv_pow, ← map_pow, hbpfix, mul_inv_cancel]
    have hcfix : α c = c := hfix c hcp
    have hcc : c ^ (p.choose 2) = 1 := by
      have hd : p ∣ p.choose 2 := Nat.Prime.dvd_choose_self
        (Fact.out : p.Prime) (by decide : 2 ≠ 0)
          (lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp))
      obtain ⟨k, hk⟩ := hd
      rw [hk, pow_mul, hcp, one_pow]
    have hh := aut_pow_apply_of_two_differences α a b c
      (by simp [b, mul_comm]) (by simp [c]) hcfix p
    rw [hα, MulAut.one_apply, hcc, mul_one] at hh
    exact mul_left_cancel (show a * b ^ p = a * 1 by simpa using hh.symm)

/-- An automorphism of order dividing an odd prime that fixes the prime
roots of an abelian p-group has all its differences among those roots. -/
public theorem IsPGroup.automorphism_prime_difference_pow_eq_one
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [IsMulCommutative A]
    (hA : IsPGroup p A) (hp : p ≠ 2) (α : MulAut A) (hα : α ^ p = 1)
    (hfix : ∀ a : A, a ^ p = 1 → α a = a) (a : A) :
    (α a * a⁻¹) ^ p = 1 := by
  obtain ⟨n, hn⟩ := hA a
  exact aut_prime_difference_aux hp α hα hfix n a hn

/-- An element of order dividing an odd prime that fixes the prime roots
of a normal abelian subgroup acts trivially modulo those roots. -/
public theorem IsPGroup.commutator_prime_root_of_fixes_abelian_roots
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    (hQ : IsPGroup p Q) (hp : p ≠ 2) (A : Subgroup Q) [A.Normal]
    [IsMulCommutative A] (x : Q) (hx : x ^ p = 1)
    (hfix : ∀ a : Q, a ∈ A → a ^ p = 1 → Commute x a)
    (a : Q) (ha : a ∈ A) : ⁅x, a⁆ ^ p = 1 := by
  let α : MulAut A := MulAut.conjNormal x
  have hα : α ^ p = 1 := by
    rw [← map_pow, hx, map_one]
  have hfixA : ∀ a : A, a ^ p = 1 → α a = a := by
    intro a ha
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hc := hfix a a.property (congrArg Subtype.val ha)
    rw [hc.eq, mul_inv_cancel_right]
  have hh := (hQ.to_subgroup A).automorphism_prime_difference_pow_eq_one
    hp α hα hfixA ⟨a, ha⟩
  simpa only [α, coe_pow, coe_mul, MulAut.conjNormal_apply, coe_inv, coe_one,
    commutatorElement_def] using congrArg Subtype.val hh
