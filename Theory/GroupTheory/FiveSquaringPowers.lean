module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Powers of an element inducing squaring on a five-subgroup

Conjugation by the nth power induces the power `2^n`. Thus the fifth
power induces the same automorphism on a subgroup of order five, the fourth
power centralizes that subgroup, and a squaring element cannot have square one. These elementary calculations
are used when removing the odd part of a normalizer lift.
Multiplying a squaring element on the left by an element of the five-subgroup
preserves its fourth power: this multiplication is conjugation by the inverse
of that element, which centralizes the fourth power.
-/

namespace Subgroup

private theorem conjugate_pow_of_squaring
    {G : Type*} [Group G] (b c : G) (h : b * c * b⁻¹ = c ^ 2)
    (n : ℕ) : b ^ n * c * (b ^ n)⁻¹ = c ^ (2 ^ n) := by
  have hi : ∀ n : ℕ, MulAut.conj (b ^ n) c = c ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_pow]
      change (b * c * b⁻¹) ^ (2 ^ n) = _
      rw [h, ← pow_mul, pow_succ']
  exact hi n

/-- The fifth power of a squaring element still squares an order-five subgroup. -/
public theorem fifth_power_squares_five
    {G : Type*} [Group G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) :
    ∀ c ∈ A, b ^ 5 * c * (b ^ 5)⁻¹ = c ^ 2 := by
  intro c hc
  have hc5 : c ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : A))
    rw [hA] at h
    exact congrArg Subtype.val h
  rw [conjugate_pow_of_squaring b c (hb c hc) 5, pow_eq_pow_mod _ hc5]
  norm_num

/-- The fourth power of a squaring element centralizes the five-subgroup. -/
public theorem fourth_power_centralizes_five
    {G : Type*} [Group G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) :
    b ^ 4 ∈ centralizer (A : Set G) := by
  apply mem_centralizer_iff.mpr
  intro c hc
  have hc5 : c ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : A))
    rw [hA] at h
    exact congrArg Subtype.val h
  have hconj := conjugate_pow_of_squaring b c (hb c hc) 4
  rw [pow_eq_pow_mod _ hc5] at hconj
  norm_num at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-- Multiplication by an element of the five-subgroup preserves the fourth
power of a squaring lift. -/
public theorem mul_fourth_power_eq_of_squares_five {G : Type*} [Group G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2)
    (c : G) (hc : c ∈ A) : (c * b) ^ 4 = b ^ 4 := by
  have he : c * b = c⁻¹ * b * c := by
    have hbc := mul_inv_eq_iff_eq_mul.mp (hb c hc)
    calc
      c * b = c⁻¹ * (c ^ 2 * b) := by group
      _ = c⁻¹ * (b * c) := by rw [hbc]
      _ = c⁻¹ * b * c := by group
  have hcomm : Commute c (b ^ 4) :=
    mem_centralizer_iff.mp (fourth_power_centralizes_five A hA b hb) c hc
  rw [he]
  calc
    (c⁻¹ * b * c) ^ 4 = c⁻¹ * b ^ 4 * c := by simpa using (conj_pow (a := c⁻¹) (b := b) (i := 4))
    _ = b ^ 4 := by rw [hcomm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]

/-- Squaring on a group of order five has order four, so its lift cannot
have square one. -/
public theorem square_ne_one_of_squares_five
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) : b ^ 2 ≠ 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  have hcG : orderOf (c : G) = 5 := by
    rw [orderOf_submonoid]
    exact hc.trans hA
  intro htwo
  have hfour := conjugate_pow_of_squaring b c (hb c c.property) 2
  simp only [htwo, inv_one, one_mul, mul_one] at hfour
  have hthree : (c : G) ^ 3 = 1 := by
    have hfour' : (c : G) ^ 4 = c := by
      simpa only [show 2 ^ 2 = 4 by norm_num] using hfour.symm
    have hh := congrArg (fun x : G => (c : G)⁻¹ * x) hfour'
    calc
      (c : G) ^ 3 = (c : G)⁻¹ * (c : G) ^ 4 := by
        rw [show (c : G) ^ 4 = (c : G) * (c : G) ^ 3 by
          rw [show 4 = 1 + 3 by norm_num, pow_add]
          simp]
        simp
      _ = 1 := by simpa using hh
  have hd := orderOf_dvd_of_pow_eq_one hthree
  rw [hcG] at hd
  norm_num at hd

/-- A fourth-power-one squaring lift has order exactly four. -/
public theorem orderOf_eq_four_of_squares_five
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) (hA : Nat.card A = 5)
    (b : G) (hb : ∀ c ∈ A, b * c * b⁻¹ = c ^ 2) (hfour : b ^ 4 = 1) :
    orderOf b = 4 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1)
    (square_ne_one_of_squares_five A hA b hb) hfour

end Subgroup
