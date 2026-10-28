/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/RationalPrimeOrder.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Prime-order rational matrices

The prime cyclotomic polynomial divides the minimal polynomial of a nonidentity
prime-order matrix, so its degree bounds the dimension from below.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/RationalPrimeOrder.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and a proof-local instance binding.
-/

public section

noncomputable section
namespace Atlas.Conway
open Polynomial

/-- The cyclotomic obstruction for a nonidentity rational matrix of prime order. -/
theorem matrix_prime_order_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (p : ℕ) (hp : p.Prime) (hpow : A ^ p = 1) (hne : A ≠ 1) :
    p - 1 ≤ Fintype.card ι := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : minpoly ℚ A ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simpa using sub_eq_zero.mpr hpow
  have hc : cyclotomic p ℚ ∣ minpoly ℚ A := by
    by_contra hn
    have hcop := ((cyclotomic.irreducible_rat hp.pos).coprime_iff_not_dvd.mpr hn).symm
    have hsmall := hcop.dvd_of_dvd_mul_left hd
    have he := (minpoly.dvd_iff (A := ℚ) (x := A)).mp hsmall
    apply hne
    exact sub_eq_zero.mp (by simpa using he)
  have he := Polynomial.natDegree_le_of_dvd
    (hc.trans (Matrix.minpoly_dvd_charpoly A)) (Matrix.charpoly_monic A).ne_zero
  simpa [natDegree_cyclotomic,Nat.totient_prime hp,Matrix.charpoly_natDegree_eq_dim] using he

end Atlas.Conway
