module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

/-!
# Congruences forced by order-three scalar matrices

Over a field of cardinality `p`, a scalar of order three forces `p ≡ 1 mod 3`.
For a three-dimensional Hermitian form with conjugation `x ↦ x^p`, an
order-three scalar isometry forces `p ≡ -1 mod 3`. The latter follows by
reading the isometry equation at a nonzero entry of the Gram matrix, which
gives the norm-one equation `a^(p+1) = 1`.

These lemmas supply the scalar arithmetic in Aschbacher–Smith, Lemma
A.3.21(c), printed pp. 55–56. They do not assert that a nonabelian subgroup
contains such a scalar; that is a separate representation-theoretic input.
-/

public section

namespace BenderSuzuki.MatrixGroups

/-- A finite field containing a scalar of order three has cardinality one
modulo three. -/
theorem card_mod_three_of_scalar_order_three {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hcard : Nat.card F = p) (a : Fˣ) (ha : orderOf a = 3) :
    p % 3 = 1 := by
  have hdiv := orderOf_dvd_natCard a
  rw [Nat.card_units, hcard, ha] at hdiv
  have hp : 0 < p := hcard ▸ Nat.card_pos
  omega

/-- An order-three scalar in the special unitary group forces the negative
congruence, using the actual Frobenius conjugation of the Hermitian form. -/
theorem HermitianForm.mod_three_of_scalar_order_three
    {F : Type*} [Field F] {p : ℕ} (J : HermitianForm 3 F)
    (hconj : ∀ x, J.conj x = x ^ p) (a : Fˣ) (ha : orderOf a = 3)
    (g : J.specialSubgroup)
    (hg : (g.val : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (a : F)) :
    p % 3 = 2 := by
  have hunitary := (J.mem_specialSubgroup_iff g.val).mp g.property |>.1
  rw [hg] at hunitary
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) (a : F)) =
      Matrix.scalar (Fin 3) (J.conj a) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hadj] at hunitary
  obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 j) hunitary
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hnorm : J.conj (a : F) * (a : F) = 1 := by
    apply mul_right_cancel₀ hj
    calc
      (J.conj (a : F) * (a : F)) * J.form 0 j =
          J.conj (a : F) * J.form 0 j * (a : F) := by ring
      _ = J.form 0 j := hentry
      _ = 1 * J.form 0 j := (one_mul _).symm
  rw [hconj, ← pow_succ] at hnorm
  have hpow : a ^ (p + 1) = 1 := Units.ext hnorm
  have hdiv := orderOf_dvd_of_pow_eq_one hpow
  rw [ha] at hdiv
  omega

end BenderSuzuki.MatrixGroups
