module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The integral cyclotomic obstruction in rank less than 36

For an integral matrix of finite order, evaluation of Φ₆₃ after reduction
modulo two is a unit whenever the rank is less than φ(63) = 36.

Over ℚ, the minimal polynomial divides Xⁿ − 1. Irreducibility and the
characteristic-polynomial degree bound allow cancellation of all cyclotomic
factors of degree greater than the rank. The remaining product has integer
coefficients and annihilates the original matrix, hence also its reduction.
A common root of a remaining factor Φ_d and Φ₆₃ in characteristic two would
have order 63, forcing 63 ∣ d and 36 ≤ φ(d). Thus the reduced product is
coprime to Φ₆₃, and Bézout supplies the matrix inverse.

This is the general arithmetic input to the integral Leech representation
in Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5, p.283.
The lattice and reference-action transports are provided separately by the
parent `IntegralSpectrum` module; there is no dependency on those actions here.
-/

public section

namespace Atlas.Conway
open Polynomial

/-- In characteristic two, a common root forces the index to be a multiple of 63. -/
private theorem small_cyclotomic_coprime (d : ℕ) (hd : 0 < d) (hdeg : Nat.totient d < 36) :
    IsCoprime (cyclotomic 63 (ZMod 2)) (cyclotomic d (ZMod 2)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero _ _).mpr
  intro K _ _ _ a
  by_contra h
  push Not at h
  have h63 : (63 : K) ≠ 0 := by
    have h0 : (63 : ZMod 2) ≠ 0 := by decide
    simpa only [_root_.map_ofNat] using
      (_root_.map_ne_zero (algebraMap (ZMod 2) K)).mpr h0
  let : NeZero (63 : K) := ⟨h63⟩
  have hr : IsPrimitiveRoot a 63 := by
    apply isRoot_cyclotomic_iff.mp
    change (cyclotomic 63 K).eval a = 0
    rw [← map_cyclotomic 63 (algebraMap (ZMod 2) K), eval_map_algebraMap]
    exact h.1
  have ha : a ^ d = 1 := by
    have he := aeval_eq_zero_of_dvd_aeval_eq_zero (cyclotomic.dvd_X_pow_sub_one d (ZMod 2)) h.2
    exact sub_eq_zero.mp (by simpa using he)
  have hh := Nat.totient_dvd_of_dvd (hr.dvd_of_pow_eq_one d ha)
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr hd) hh
  have hnum : Nat.totient 63 = 36 := by decide
  omega

/-- Cancel every irreducible factor whose degree exceeds the matrix rank. -/
private theorem rational_annihilator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (n : ℕ) (hn : 0 < n) (hpow : A ^ n = 1) :
    aeval A (∏ d ∈ n.divisors.filter (fun d => Nat.totient d ≤ Fintype.card ι),
      cyclotomic d ℚ) = 0 := by
  have hdiv : minpoly ℚ A ∣ ∏ d ∈ n.divisors, cyclotomic d ℚ := by
    rw [prod_cyclotomic_eq_X_pow_sub_one hn]
    apply minpoly.dvd
    simpa using sub_eq_zero.mpr hpow
  have hcop : IsCoprime (minpoly ℚ A)
      (∏ d ∈ n.divisors.filter (fun d => ¬ Nat.totient d ≤ Fintype.card ι),
        cyclotomic d ℚ) := by
    apply IsCoprime.prod_right
    intro d hd
    obtain ⟨hdn, hdeg⟩ := Finset.mem_filter.mp hd
    apply IsCoprime.symm
    apply (cyclotomic.irreducible_rat (Nat.pos_of_mem_divisors hdn)).coprime_iff_not_dvd.mpr
    intro hdm
    apply hdeg
    have hle := Polynomial.natDegree_le_of_dvd
      (hdm.trans (Matrix.minpoly_dvd_charpoly A)) (Matrix.charpoly_monic A).ne_zero
    simpa [natDegree_cyclotomic, Matrix.charpoly_natDegree_eq_dim] using hle
  apply (minpoly.dvd_iff (A := ℚ) (x := A)).mp
  apply hcop.dvd_of_dvd_mul_right
  rwa [Finset.prod_filter_mul_prod_filter_not]

/-- The rational annihilator has integral coefficients, so injectivity descends it to ℤ. -/
private theorem integral_annihilator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (n : ℕ) (hn : 0 < n) (hpow : A ^ n = 1) :
    aeval A (∏ d ∈ n.divisors.filter (fun d => Nat.totient d ≤ Fintype.card ι),
      cyclotomic d ℤ) = 0 := by
  let f := (Int.castRingHom ℚ).mapMatrix (m := ι)
  let p : ℤ[X] := ∏ d ∈ n.divisors.filter (fun d => Nat.totient d ≤ Fintype.card ι),
    cyclotomic d ℤ
  have hpowQ : f A ^ n = 1 := by rw [← map_pow, hpow, map_one]
  have hQ := rational_annihilator (f A) n hn hpowQ
  have he : aeval (f A) p = 0 := by
    rw [aeval_eq_aeval_map (φ := Int.castRingHom ℚ) (Subsingleton.elim _ _)]
    simpa only [p, Polynomial.map_prod, map_cyclotomic_int] using hQ
  have hf : f (aeval A p) = f 0 := by
    rw [map_zero]
    exact (aeval_algHom_apply f.toIntAlgHom A p).symm.trans he
  exact Matrix.map_injective (Int.cast_injective (α := ℚ)) hf

/-- A finite-order integral matrix of rank less than 36 has invertible Φ₆₃
after reduction modulo two. -/
theorem integralMatrix_cyclotomic63_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : IsOfFinOrder A) (hdim : Fintype.card ι < 36) :
    IsUnit (aeval (A.map (Int.castRingHom (ZMod 2))) (cyclotomic 63 ℤ)) := by
  obtain ⟨n, hn, hpow⟩ := hA.exists_pow_eq_one
  let s := n.divisors.filter (fun d => Nat.totient d ≤ Fintype.card ι)
  let f := (Int.castRingHom (ZMod 2)).mapMatrix (m := ι)
  have hannZ := integral_annihilator A n hn hpow
  have hann : aeval (f A) (∏ d ∈ s, cyclotomic d (ZMod 2)) = 0 := by
    have he := congrArg f hannZ
    rw [map_zero] at he
    have he := (aeval_algHom_apply f.toIntAlgHom A _).trans he
    rw [aeval_eq_aeval_map (φ := Int.castRingHom (ZMod 2)) (Subsingleton.elim _ _)] at he
    simpa only [s, Polynomial.map_prod, map_cyclotomic_int, RingHom.toIntAlgHom_apply] using he
  have hcop : IsCoprime (cyclotomic 63 (ZMod 2)) (∏ d ∈ s, cyclotomic d (ZMod 2)) := by
    apply IsCoprime.prod_right
    intro d hd
    obtain ⟨hdn, hdeg⟩ := Finset.mem_filter.mp hd
    exact small_cyclotomic_coprime d (Nat.pos_of_mem_divisors hdn) (lt_of_le_of_lt hdeg hdim)
  obtain ⟨u, v, huv⟩ := hcop
  have he := congrArg (aeval (f A)) huv
  simp only [map_add, map_mul, hann, mul_zero, add_zero, map_one] at he
  rw [aeval_eq_aeval_map (φ := Int.castRingHom (ZMod 2)) (Subsingleton.elim _ _),
    map_cyclotomic_int]
  exact IsUnit.of_mul_eq_one_right _ he

end Atlas.Conway
