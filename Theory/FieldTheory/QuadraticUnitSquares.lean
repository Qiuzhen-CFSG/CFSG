module

public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Mathlib.Algebra.CharP.CharAndCard
open Polynomial
/-!
# Unit squares in a quadratic finite field

The two-element coefficient group identifies its nonidentity element with
Frobenius. A cyclic unit generator then rules out fixing or inverting all
unit squares when the defining prime is greater than three.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
namespace FiniteField
 theorem square_ringAut_apply_of_ne_one
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : σ ≠ 1) (x : F) : σ x = x ^ p := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by simpa only [← Nat.card_eq_fintype_card] using hF)
  let φ : F ≃+* F := frobeniusEquiv F p
  have hφ : φ ≠ 1 := by
    intro he
    have hc := Polynomial.card_le_degree_of_subset_roots (R := F)
      (p := X ^ p - X) (Z := Finset.univ) (by
        intro a _
        rw [mem_roots']
        constructor
        · intro hz
          have hh := congrArg (fun q : F[X] => q.coeff 1) hz
          have hp := (Fact.out : p.Prime).one_lt
          simp [coeff_X_pow, ne_of_lt hp] at hh
        · rw [IsRoot, eval_sub, eval_pow, eval_X]
          have hh := DFunLike.congr_fun he a
          exact sub_eq_zero.mpr hh)
    have hp := (Fact.out : p.Prime).one_lt
    have hb : (X ^ p - X : F[X]).natDegree ≤ p := by
      apply (natDegree_sub_le _ _).trans
      simp [Nat.one_le_of_lt hp]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at hc
    have hle := hc.trans hb
    nlinarith
  have hcard := card_ringAut_of_card_prime_pow (Fact.out : p.Prime) hF
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp hcard
  have he : σ = φ := (hz σ hσ).trans (hz φ hφ).symm
  rw [he]
  rfl
/-- An automorphism of an odd square field larger than nine cannot invert or
fix all unit squares unless it is the identity. -/
theorem ringAut_eq_one_of_unit_squares_fixed_or_inverted
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ 2) (hp : 3 < p) (σ : F ≃+* F)
    (hact : (∀ a : Fˣ, Units.map σ.toRingHom (a ^ 2) = a ^ 2) ∨
      (∀ a : Fˣ, Units.map σ.toRingHom (a ^ 2) = (a ^ 2)⁻¹)) : σ = 1 := by
  by_contra hσ
  have hmap (a : Fˣ) : Units.map σ.toRingHom a = a ^ p := by
    apply Units.ext
    exact square_ringAut_apply_of_ne_one hF σ hσ a
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Fˣ)
  have ha' : orderOf a = p ^ 2 - 1 := by simpa only [Nat.card_units, hF] using ha
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel hp2
  have hsubp : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  rcases hact with hact | hact
  · have he : a ^ (2 * p) = a ^ 2 := by
      rw [pow_mul, ← hmap]
      exact hact a
    have he' : a ^ (2 * (p - 1)) = 1 := by
      apply mul_right_cancel (b := a ^ 2)
      rw [← pow_add, one_mul]
      have hn : 2 * (p - 1) + 2 = 2 * p := by omega
      rwa [hn]
    have hd := orderOf_dvd_of_pow_eq_one he'
    rw [ha'] at hd
    have hb := Nat.le_of_dvd (by omega : 0 < 2 * (p - 1)) hd
    nlinarith
  · have he : a ^ (2 * p) = (a ^ 2)⁻¹ := by
      rw [pow_mul, ← hmap]
      exact hact a
    have he' : a ^ (2 * (p + 1)) = 1 := by
      rw [Nat.mul_add, Nat.mul_one, pow_add, he, inv_mul_cancel]
    have hd := orderOf_dvd_of_pow_eq_one he'
    rw [ha'] at hd
    have hb := Nat.le_of_dvd (by omega : 0 < 2 * (p + 1)) hd
    nlinarith
end FiniteField
