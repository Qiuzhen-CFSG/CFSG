module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.Conditions
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.PowerConjugator
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.InvolutionCoverage

/-!
# Reducing the normalized Held pairs to two conjugacy-class calculations

An explicit inner conjugation squares `ab`. Its iterates send every nonzero
power of `ab` to the power with exponent 1 or 3. The zero exponent cannot
satisfy the source relation `y⁷ = 1` when `x` has order two. Conjugation
transports all seven relations and the common fixed point of the three
literal marked words, so the two reduced exponents suffice.

The existing Sylow-word fusion theorem supplies coverage of all involutions
by the classes of `a` and `(ab³)⁴`. The final theorem below therefore retains
only the fixed-point calculation on each whole class as explicit premises.
These two finite obligations are not asserted here. This module owns their
eventual assembly into `NormalizedPairFixedPoint`.

Source: John Bray's `Model/Source/HeG1-P1.M`, the seven uncommented
relators and `M1 = <x, x^(y²), x^(y⁻²)>`, with Magma conjugation
`x^y = y⁻¹*x*y`; the carrier is the retained ATLAS representation
`HeG1-p2058B0`.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

private theorem pairFixes_conj (g x y : He) (p : Fin 2058) (hp : PairFixes x y p) :
    PairFixes (MulAut.conj g x) (MulAut.conj g y) (representation g p) := by
  have hfix (z : He) (hz : representation z p = p) :
      representation (MulAut.conj g z) (representation g p) = representation g p := by
    simp only [MulAut.conj_apply, map_mul, map_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, hz]
  refine ⟨hfix x hp.1, ?_, ?_⟩
  · simpa only [map_mul, map_pow, map_inv] using hfix ((y ^ 2)⁻¹ * x * y ^ 2) hp.2.1
  · simpa only [map_mul, map_pow, map_inv] using hfix (y ^ 2 * x * (y ^ 2)⁻¹) hp.2.2

private theorem conj_powerDoubler (d : He)
    (hd : MulAut.conj d (a * b) = (a * b) ^ 2) (n m : ℕ) :
    MulAut.conj (d ^ n) ((a * b) ^ m) = (a * b) ^ (2 ^ n * m) := by
  have h (n : ℕ) : MulAut.conj (d ^ n) (a * b) = (a * b) ^ (2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul (MulAut.conj : He →* MulAut He), MulAut.mul_apply, hd, map_pow, ih, ← pow_mul, pow_succ]
  rw [map_pow, h, ← pow_mul]

private theorem exponent_reduction : ∀ k : Fin 17, k ≠ 0 →
    ∃ n : Fin 8, (2 ^ n.val * k.val) % 17 = 1 ∨ (2 ^ n.val * k.val) % 17 = 3 := by
  decide +kernel

private theorem no_relations_at_zero (x : He) (hx : orderOf x = 2)
    (hr : ∀ i : Fin 7, relationWord x (x * (a * b) ^ (0 : Fin 17).val) i = 1) : False := by
  have hp : x ^ 7 = 1 := by simpa only [relationWord, Fin.val_zero, pow_zero, mul_one] using hr 1
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx] at hd
  omega

/-- The literal pair calculation for exponents 1 and 3 implies it for every
power of `ab`, using the kernel-checked power-doubling conjugator. -/
public theorem normalizedPairFixedPoint_of_one_three
    (hsmall : ∀ k : Fin 17, k = 1 ∨ k = 3 → ∀ x : He, orderOf x = 2 →
      (∀ i : Fin 7, relationWord x (x * (a * b) ^ k.val) i = 1) →
      ∃ p : Fin 2058, PairFixes x (x * (a * b) ^ k.val) p) :
    NormalizedPairFixedPoint := by
  obtain ⟨d, hd⟩ := exists_powerDoubler
  intro k x hx hr
  by_cases hk : k = 0
  · subst k
    exact (no_relations_at_zero x hx hr).elim
  obtain ⟨n, hn⟩ := exponent_reduction k hk
  let r : Fin 17 := ⟨(2 ^ n.val * k.val) % 17, Nat.mod_lt _ (by decide)⟩
  have hrsmall : r = 1 ∨ r = 3 := by
    rcases hn with hn | hn
    · exact Or.inl (Fin.ext hn)
    · exact Or.inr (Fin.ext hn)
  let g := d ^ n.val
  let f := MulAut.conj g
  have hc : f ((a * b) ^ k.val) = (a * b) ^ r.val := by
    rw [conj_powerDoubler d hd]
    symm
    simpa only [orderOf_ab] using pow_mod_orderOf (a * b) (2 ^ n.val * k.val)
  have hy : f (x * (a * b) ^ k.val) = f x * (a * b) ^ r.val := by
    rw [map_mul, hc]
  have hr' : ∀ i : Fin 7, relationWord (f x) (f x * (a * b) ^ r.val) i = 1 := by
    intro i
    have h := congrArg f.toMonoidHom (hr i)
    rw [map_relationWord, map_one] at h
    change relationWord (f x) (f (x * (a * b) ^ k.val)) i = 1 at h
    rwa [hy] at h
  obtain ⟨p, hp⟩ := hsmall r hrsmall (f x) ((f.orderOf_eq x).trans hx) hr'
  have hp' := pairFixes_conj g⁻¹ (f x) (f (x * (a * b) ^ k.val)) p (by simpa only [hy] using hp)
  refine ⟨representation g⁻¹ p, ?_⟩
  simpa only [f, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    MulAut.one_apply] using hp'

/-- Conditional assembly. All three premises must be discharged to establish
the normalized-pair fixed-point theorem for the actual Held carrier. -/
public theorem normalizedPairFixedPoint_of_calculations
    (hcoverage : InvolutionCoverage)
    (hfirst : ClassCalculation a)
    (hsecond : ClassCalculation secondSeed) : NormalizedPairFixedPoint := by
  apply normalizedPairFixedPoint_of_one_three
  intro k hk x hx hr
  rcases hcoverage x hx with h | h
  · exact hfirst k hk x h hr
  · exact hsecond k hk x h hr

/-- All involutions and all seventeen exponents are covered. Only the two
whole-class fixed-point calculations remain for final assembly. -/
public theorem normalizedPairFixedPoint_of_classCalculations
    (hfirst : ClassCalculation a)
    (hsecond : ClassCalculation secondSeed) : NormalizedPairFixedPoint :=
  normalizedPairFixedPoint_of_calculations involutionCoverage hfirst hsecond

end Held.Realization.MarkedConjugacy.NormalizedPairs
