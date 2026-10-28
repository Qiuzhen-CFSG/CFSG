module

public import Theory.Representation.SL2.PrimeFieldParameters
public import Theory.Combinatorics.PeriodicDigitProduct

/-!
# Frobenius-Orbit Dimension Parameters

For a nontrivial irreducible GF(p)-representation of SL2(K), with p odd and
|K| = p^m for m positive, the dimension is s*b^t with m=s*t and s,t positive,
b at least two. If -I is outside the kernel, t is odd and b is even.

The actual prime-field parameter theorem identifies s with the Schur-field
degree and provides a nonzero weight n whose digit product gives the remaining
dimension. Its Frobenius divisibility forces repetition of a digit block of
length s. The periodic-digit theorem supplies b and the parity refinement.
All classification and descent inputs are already proved for the actual
representation; this module only assembles them.

These are the parameters used after Fong--Wong (1.15), Nagoya Math. J.
36 (1969), p. 149. The final numerical inequalities are applied separately in
LowDegreeIrreducible to obtain the full statement (1E).
-/

open scoped MatrixGroups MonoidAlgebra

namespace Representation.SL2

public theorem exists_frobenius_orbit_parameters {K V : Type*} [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : Representation (ZMod p) SL(2,K) V)
    [ρ.IsIrreducible] (hp : Odd p) (hρ : ∃ g, ρ g ≠ 1)
    (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card K = p ^ m) :
    ∃ s t b : ℕ, 0 < s ∧ 0 < t ∧ 2 ≤ b ∧ m = s*t ∧
      Module.finrank (ZMod p) V = s*b^t ∧
      ((-1 : SL(2,K)) ∉ ρ.ker → Odd t ∧ Even b) := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact (by decide : ¬ Odd 2) hp
  let s := Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule)
  obtain ⟨hs, n, hn, hsdiv, hperiod, hdim, hodd⟩ :=
    exists_primeField_highestWeight_parameters p ρ hp2 hρ m hcard
  obtain ⟨t, hmt⟩ := hsdiv
  have ht : 0 < t := by
    by_contra! h
    have : t = 0 := Nat.eq_zero_of_le_zero h
    simp only [this, mul_zero] at hmt
    exact hm hmt
  have hnlt : n.val < p ^ (s*t) := by
    rw [← hmt, ← hcard]
    exact n.isLt
  have hper : (p ^ (s*t) - 1) ∣ n.val * (p ^ s - 1) := by
    simpa only [hcard, hmt] using hperiod
  obtain ⟨b, hb, hprod, hpar⟩ := Nat.exists_digit_product_pow_of_period p s t n.val
    (Fact.out : p.Prime).two_le hs ht hn hnlt hper
  refine ⟨s, t, b, hs, ht, hb, hmt, ?_, fun hneg => hpar hp (hodd hneg)⟩
  rw [hdim, hmt, hprod]

end Representation.SL2
