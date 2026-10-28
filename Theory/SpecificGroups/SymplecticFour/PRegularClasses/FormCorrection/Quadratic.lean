module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Quadratic form ratios in dimension four

Writing an alternating four-by-four matrix using its six upper entries gives
T² + cT + dI = 0 for T = JA; d is its Pfaffian. If c is nonzero, the finite
characteristic-two field supplies a square root which is a linear polynomial
in T. If c is zero, a scalar shift of T is square-zero. These exhaustive cases
do not impose any condition on eigenvalue multiplicities.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection

open Matrix
variable {F : Type*} [Field F] [CharP F 2]
local notation "M" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F
local notation "J₄" => Matrix.J (Fin 2) F

/-- The ratio of alternating forms in dimension four satisfies a quadratic. -/
public theorem ratio_quadratic (A : M) (hA : A.toBilin'.IsAlt) :
    ∃ c d : F, (J₄ * A) ^ 2 + c • (J₄ * A) + d • (1 : M) = 0 := by
  have hs (i j) : A j i = A i j := by
    have h := hA.neg_eq (Pi.single i 1) (Pi.single j 1)
    simpa [CharTwo.neg_eq] using h.symm
  have hd (i) : A i i = 0 := by
    simpa using hA.self_eq_zero (Pi.single i 1)
  refine ⟨A (.inl 0) (.inr 0) + A (.inl 1) (.inr 1),
    A (.inl 0) (.inl 1) * A (.inr 0) (.inr 1) +
    A (.inl 0) (.inr 0) * A (.inl 1) (.inr 1) +
    A (.inl 0) (.inr 1) * A (.inl 1) (.inr 0), ?_⟩
  have h10 := hs (.inl 0) (.inl 1)
  have h20 := hs (.inl 0) (.inr 0)
  have h30 := hs (.inl 0) (.inr 1)
  have h21 := hs (.inl 1) (.inr 0)
  have h31 := hs (.inl 1) (.inr 1)
  have h32 := hs (.inr 0) (.inr 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.J, Matrix.mul_apply, Fin.sum_univ_two,
      Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
      hd, h10, h20, h30, h21, h31, h32, CharTwo.neg_eq] <;>
    ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
section Scalar
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CharP (Matrix n n F) 2 :=
  charP_of_injective_algebraMap (algebraMap F (Matrix n n F)).injective 2

/-- Squaring a scalar linear polynomial in a matrix in characteristic two. -/
public theorem linear_sq (T : Matrix n n F) (u v : F) :
    (u • T + v • (1 : Matrix n n F)) ^ 2 = u ^ 2 • T ^ 2 + v ^ 2 • (1 : Matrix n n F) := by
  have hc : Commute (u • T) (v • (1 : Matrix n n F)) := by
    change (u • T) * (v • 1) = (v • 1) * (u • T)
    simp [smul_smul, mul_comm]
  rw [hc.add_sq]
  simp [smul_pow, CharTwo.two_eq_zero]

/-- A quadratic relation with nonzero linear coefficient gives a polynomial square root. -/
public theorem exists_linear_square_root [Finite F] (T : Matrix n n F) (c d : F) (hc : c ≠ 0)
    (hq : T ^ 2 + c • T + d • (1 : Matrix n n F) = 0) :
    ∃ u v : F, (u • T + v • (1 : Matrix n n F)) ^ 2 = T := by
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) c⁻¹
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) (c⁻¹ * d)
  change u ^ 2 = c⁻¹ at hu
  change v ^ 2 = c⁻¹ * d at hv
  have he : T ^ 2 + d • (1 : Matrix n n F) = c • T := by
    apply CharTwo.add_eq_zero.mp
    simpa only [add_assoc, add_left_comm, add_comm] using hq
  refine ⟨u, v, ?_⟩
  rw [linear_sq, hu, hv, mul_smul, ← smul_add, he, smul_smul, inv_mul_cancel₀ hc, one_smul]
end Scalar
end Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection
