module

public import Theory.Representation.SL2.PrimeFieldParameters
public import Theory.Representation.SL2.OrbitDimensionBounds
public import Theory.Combinatorics.PeriodicDigitProduct

/-!
# The Schur Degree in Minimal Faithful Dimension

Let K have order p^m with p odd and m positive. If an irreducible
GF(p)-representation of SL2(K) has dimension 2m and -I is outside its kernel,
then its actual Schur endomorphism field has degree m over GF(p).

The prime-field parameter theorem uses the actual Schur degree s, and gives
a nonzero odd highest weight with s dividing m. Writing m=s*t, periodicity
of its digits expresses the dimension as s*b^t with t odd and b at least two.
The minimal-orbit arithmetic forces t=1, hence s=m. We use the theorem
retaining the actual Schur degree, rather than an unspecified existential
orbit parameter.

This is the degree computation needed for the fixed-space equality in
Alperin--Brauer--Gorenstein II.4, Lemma 18(ii), article pp. 45--46.
-/

open scoped MatrixGroups MonoidAlgebra

namespace Representation.SL2

public theorem endField_finrank_eq_of_minimal {K V : Type*} [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : Representation (ZMod p) SL(2,K) V)
    [ρ.IsIrreducible] (hp : Odd p) (hneg : (-1 : SL(2,K)) ∉ ρ.ker)
    (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card K = p ^ m)
    (hdim : Module.finrank (ZMod p) V = 2*m) :
    Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule) = m := by
  have hp2 : p ≠ 2 := by intro h; subst p; exact (by decide : ¬ Odd 2) hp
  let s := Module.finrank (ZMod p) (Module.End (ZMod p)[SL(2,K)] ρ.asModule)
  obtain ⟨hs, n, hn, hsdiv, hperiod, hd, hodd⟩ :=
    exists_primeField_highestWeight_parameters p ρ hp2 ⟨-1, hneg⟩ m hcard
  obtain ⟨t, hmt⟩ := hsdiv
  have ht : 0 < t := by
    by_contra! h
    have : t = 0 := Nat.eq_zero_of_le_zero h
    simp only [this, mul_zero] at hmt
    exact hm hmt
  have hnlt : n.val < p ^ (s*t) := by rw [← hmt, ← hcard]; exact n.isLt
  have hper : (p ^ (s*t) - 1) ∣ n.val * (p ^ s - 1) := by
    simpa only [hcard, hmt] using hperiod
  obtain ⟨b, hb, hprod, hpar⟩ := Nat.exists_digit_product_pow_of_period p s t n.val
    (Fact.out : p.Prime).two_le hs ht hn hnlt hper
  have heq : s*b^t = 2*(s*t) := by
    rw [hdim, hmt, hprod] at hd
    exact hd.symm
  have htone := (orbit_dimension_minimal_parameters hs (hpar hp (hodd hneg)).1 hb heq).1
  simpa only [htone, mul_one] using hmt.symm

end Representation.SL2
