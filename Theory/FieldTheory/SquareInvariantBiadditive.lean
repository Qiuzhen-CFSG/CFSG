module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Additive pairings invariant under square scalars

An additive pairing on a finite field of odd characteristic, invariant under
simultaneous multiplication by every nonzero square, vanishes if the field
has more than nine elements. No linearity over the field is assumed.

Move a square from one argument to the other as its inverse. Polarizing
`(a + 1)^2 + (a - 1)^2 = 2*a^2 + 2` then forces, for a nonzero pairing,
`a^6 - 2*a^4 - 2*a^2 + 1 = 0` away from `0, 1, -1`. The polynomial root
bound gives the result. This supplies the torus calculation for central
covers of PSL₂ in Aschbacher–Smith I.1.3(1), via GLS3 §6.1.
-/

namespace FiniteField

open Polynomial

variable {F A : Type*} [Field F] [Finite F] [AddCommGroup A]

/-- Square-invariance forces an additive pairing to vanish for odd fields
with more than nine elements. -/
public theorem biadditive_eq_zero_of_square_invariant (h2 : (2 : F) ≠ 0) (hcard : 9 < Nat.card F)
    (B : F →+ F →+ A)
    (hinv : ∀ a : F, a ≠ 0 → ∀ x y, B (a^2*x) (a^2*y) = B x y) :
    ∀ x y, B x y = 0 := by
  classical
  by_contra hzero
  push Not at hzero
  obtain ⟨x₀, y₀, hnonzero⟩ := hzero
  have hbal (a : F) (ha : a ≠ 0) (x y : F) :
      B (a^2*x) y = B x (a⁻¹^2*y) := by
    have h := hinv a ha x (a⁻¹^2*y)
    simpa [mul_assoc, ← mul_pow, ha] using h
  have hrel (a : F) (ha : a ≠ 0) (hap : a+1 ≠ 0) (ham : a-1 ≠ 0) (x y : F) :
      B x (((a+1)⁻¹^2 + (a-1)⁻¹^2 - (a⁻¹^2+a⁻¹^2) - (1+1))*y) = 0 := by
    have heq : (a+1)^2*x + (a-1)^2*x = (a^2*x+a^2*x)+(x+x) := by ring
    have h := congrArg (fun z => B z y) heq
    simp only [map_add, AddMonoidHom.add_apply] at h
    rw [hbal _ hap, hbal _ ham, hbal _ ha] at h
    simp only [sub_mul, add_mul, one_mul, map_sub, map_add]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h))
  have hr (a : F) (ha : a ≠ 0) (hap : a+1 ≠ 0) (ham : a-1 ≠ 0) :
      (a+1)⁻¹^2 + (a-1)⁻¹^2 - (a⁻¹^2+a⁻¹^2) - (1+1) = 0 := by
    by_contra hc
    have h := hrel a ha hap ham x₀
      (((a+1)⁻¹^2 + (a-1)⁻¹^2 - (a⁻¹^2+a⁻¹^2) - (1+1))⁻¹*y₀)
    simp only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h
    exact hnonzero h
  have hpoly (a : F) (ha : a ≠ 0) (hap : a+1 ≠ 0) (ham : a-1 ≠ 0) :
      a^6 - 2*a^4 - 2*a^2 + 1 = 0 := by
    have h := hr a ha hap ham
    have heq : ((a+1)⁻¹^2 + (a-1)⁻¹^2 - (a⁻¹^2+a⁻¹^2) - (1+1)) *
        (a^2*(a+1)^2*(a-1)^2) = -2*(a^6 - 2*a^4 - 2*a^2 + 1) := by
      field_simp
      ring
    rw [h, zero_mul] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (neg_ne_zero.mpr h2)
  let P : F[X] := X * (X^2-1) * (X^6-2*X^4-2*X^2+1)
  have hP : P.natDegree = 9 := by dsimp [P]; compute_degree!
  have heval (a : F) : P.eval a = 0 := by
    dsimp [P]
    simp only [eval_mul, eval_X, eval_sub, eval_pow, eval_one, eval_add, eval_ofNat]
    by_cases ha : a = 0
    · simp [ha]
    by_cases hap : a+1 = 0
    · have : a = -1 := eq_neg_of_add_eq_zero_left hap
      simp [this]
    by_cases ham : a-1 = 0
    · simp [sub_eq_zero.mp ham]
    rw [hpoly a ha hap ham, mul_zero]
  let := Fintype.ofFinite F
  have hPzero : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    Function.injective_id heval (by simpa [hP, ← Nat.card_eq_fintype_card] using hcard)
  simp [hPzero] at hP

end FiniteField
