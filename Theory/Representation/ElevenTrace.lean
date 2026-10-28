module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TracePowers
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Binary traces on fixed-point-free elements of order eleven

In characteristic two, suppose an element of order eleven is conjugate to its
fourth power and fixes no vector of a representation of even dimension. The
sum of its eleven powers is zero. Conjugacy groups the ten nonidentity powers
into two orbits of length five; their traces are respectively `t` and `t²`.
Taking the trace of the geometric sum therefore gives `t² = t`.

This uses the actual operator and its kernel, over an arbitrary characteristic-
two field. It does not assume a field of definition or identify any irreducible
representation. The consumer is the Higman--Sims degree-twenty calculation in
Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1, p.16.
-/

public section
namespace Representation
open scoped BigOperators

variable {K G W : Type*} [Field K] [CharP K 2] [Group G]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (τ : Representation K G W)

omit [CharP K 2] [FiniteDimensional K W] in
private theorem char_eq_of_conj {a b : G} (h : IsConj a b) :
    τ.character a = τ.character b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, char_conj]

/-- Fourth-power conjugacy and a vanishing fixed space force a binary trace
at order eleven when the dimension vanishes in the coefficient field. -/
theorem character_sq_eq_of_order_eleven_fixedFree (g : G) (ho : orderOf g = 11)
    (hc : IsConj g (g ^ 4))
    (hfree : LinearMap.ker (τ g - 1) = ⊥)
    (hd : (Module.finrank K W : K) = 0) : τ.character g ^ 2 = τ.character g := by
  have hp : (τ g) ^ 11 = 1 := by
    rw [← map_pow, ← ho, pow_orderOf_eq_one, map_one]
  have hsum : (∑ i ∈ Finset.range 11, (τ g) ^ i) = 0 := by
    ext v
    apply (LinearMap.ker_eq_bot.mp hfree)
    have h := congrArg (fun f : Module.End K W => f v) (mul_geom_sum (τ g) 11)
    rw [hp, sub_self] at h
    simpa using h
  have ht : (∑ i ∈ Finset.range 11, τ.character (g ^ i)) = 0 := by
    have h := congrArg (LinearMap.trace K W) hsum
    simpa only [map_sum, map_zero, map_pow, Representation.character] using h
  have hpower (n : ℕ) : τ.character (g ^ n) = τ.character (g ^ ((4 * n) % 11)) := by
    have h := char_eq_of_conj τ (IsConj.pow n hc)
    rw [← pow_mul, ← pow_mod_orderOf g (4 * n), ho] at h
    exact h
  have h3 : τ.character (g ^ 3) = τ.character g := by simpa using hpower 3
  have h4 : τ.character (g ^ 4) = τ.character g := (char_eq_of_conj τ hc).symm
  have h5 : τ.character (g ^ 5) = τ.character g := by
    have h := hpower 4
    norm_num at h
    exact h.symm.trans h4
  have h9 : τ.character (g ^ 9) = τ.character g := by
    have h := hpower 9
    norm_num at h
    exact h.trans h3
  have h8 : τ.character (g ^ 8) = τ.character (g ^ 2) := by
    have h := hpower 2
    norm_num at h
    exact h.symm
  have h10 : τ.character (g ^ 10) = τ.character (g ^ 2) := by
    have h := hpower 8
    norm_num at h
    exact h.symm.trans h8
  have h7 : τ.character (g ^ 7) = τ.character (g ^ 2) := by
    have h := hpower 10
    norm_num at h
    exact h.symm.trans h10
  have h6 : τ.character (g ^ 6) = τ.character (g ^ 2) := by
    have h := hpower 6
    norm_num at h
    exact h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    pow_one, char_one, hd, h3, h4, h5, h6, h7, h8, h9, h10] at ht
  have heq : τ.character (g ^ 2) = τ.character g := by
    have h : τ.character g + τ.character (g ^ 2) = 0 := by
      linear_combination ht - 2 * (CharTwo.add_self_eq_zero (τ.character g)) -
        2 * (CharTwo.add_self_eq_zero (τ.character (g ^ 2)))
    exact (CharTwo.add_eq_zero.mp h).symm
  simpa only [character_sq_charTwo] using heq

end Representation
