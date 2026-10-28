module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Reduced

/-!
# Characteristic-two traces and power fusion

The off-diagonal terms in the trace of a squared matrix cancel in pairs.
Consequently, taking a power of two commutes with taking the character of a
representation. If two such powers of a group element are conjugate, injectivity
of Frobenius gives a period for its character value.

The application is the quadratic trace field in the Hall--Janko calculation
of Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1, p.16.
The algebraic argument here is independent of the group and its degree.
-/

public section

namespace Matrix

/-- Squaring commutes with matrix trace in characteristic two. -/
theorem trace_sq_charTwo {K n : Type*} [CommRing K] [CharP K 2]
    [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    Matrix.trace (M ^ 2) = Matrix.trace M ^ 2 := by
  classical
  have hoff : (∑ ij : n × n,
      if ij.1 = ij.2 then 0 else M ij.1 ij.2 * M ij.2 ij.1) = 0 := by
    apply Finset.sum_involution (fun ij _ => ij.swap)
    · intro ij _
      dsimp
      by_cases h : ij.1 = ij.2
      · simp [h]
      · simp [h, Ne.symm h, mul_comm, CharTwo.add_self_eq_zero]
    · intro ij _ hne heq
      have h : ij.1 = ij.2 := (congrArg Prod.fst heq).symm
      exact hne (by simp [h])
    · intro ij _
      exact Prod.swap_swap ij
    · intro ij _
      exact Finset.mem_univ _
  calc
    Matrix.trace (M ^ 2) = ∑ i, ∑ j, M i j * M j i := by
      simp [Matrix.trace, pow_two, Matrix.mul_apply]
    _ = ∑ i, ∑ j, ((if i = j then M i i ^ 2 else 0) +
        (if i = j then 0 else M i j * M j i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h, pow_two]
    _ = (∑ i, M i i ^ 2) +
        (∑ ij : n × n, if ij.1 = ij.2 then 0 else M ij.1 ij.2 * M ij.2 ij.1) := by
      simp [Finset.sum_add_distrib, Fintype.sum_prod_type]
    _ = Matrix.trace M ^ 2 := by
      rw [hoff, add_zero]
      exact (sum_pow_char 2 _ _).symm

end Matrix

namespace Representation

variable {K G U : Type*} [Field K] [CharP K 2]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]

section Monoid
variable [Monoid G]

/-- The character at a square is the square of the character value. -/
theorem character_sq_charTwo (ρ : Representation K G U) (g : G) :
    ρ.character (g ^ 2) = ρ.character g ^ 2 := by
  classical
  let b := Module.finBasis K U
  simp only [Representation.character, map_pow,
    LinearMap.trace_eq_matrix_trace K b, ← LinearMap.toMatrix_pow]
  exact Matrix.trace_sq_charTwo _

/-- Iterated squaring commutes with the character in characteristic two. -/
theorem character_two_pow_charTwo (ρ : Representation K G U) (g : G) (n : ℕ) :
    ρ.character (g ^ (2 ^ n)) = ρ.character g ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, character_sq_charTwo, ih, ← pow_mul]

end Monoid

/-- Fusion of powers with Frobenius exponents differing by two forces the
character value into the quadratic fixed field. -/
theorem character_four_of_power_fusion [Group G] (ρ : Representation K G U) (g : G)
    (n : ℕ) (h : IsConj (g ^ (2 ^ n)) (g ^ (2 ^ (n + 2)))) :
    ρ.character g ^ 4 = ρ.character g := by
  have ht : ρ.character (g ^ (2 ^ n)) = ρ.character (g ^ (2 ^ (n + 2))) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    rw [← hc, char_conj]
  simp only [character_two_pow_charTwo] at ht
  apply iterateFrobenius_inj K 2 n
  change (ρ.character g ^ 4) ^ (2 ^ n) = ρ.character g ^ (2 ^ n)
  rw [← pow_mul]
  simpa [pow_add, Nat.mul_comm] using ht.symm

end Representation
