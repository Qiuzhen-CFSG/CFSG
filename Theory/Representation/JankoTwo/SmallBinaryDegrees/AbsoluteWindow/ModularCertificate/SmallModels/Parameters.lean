module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Arithmetic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Two coefficient embeddings and their separating values

Algebraic closure supplies a root of X²-X-1. In characteristic two its square
is another root, and the two are distinct. The nonbinary coefficient codes
therefore distinguish the two evaluated matrix actions by trace.

Source: the two Frobenius-conjugate ATLAS candidates in each of degrees 6 and
14. This proves the scalar part of their separation, without a character table.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Polynomial Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem exists_parameter [IsAlgClosed F] : ∃ t : F, t ^ 2 = t + 1 := by
  have hd : (X ^ 2 - X - 1 : F[X]).natDegree = 2 := by compute_degree; exact one_ne_zero
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (X ^ 2 - X - 1 : F[X]) (by
    intro h
    have hz : (X ^ 2 - X - 1 : F[X]).natDegree = 0 :=
      Polynomial.natDegree_eq_of_degree_eq_some h
    omega)
  refine ⟨t, ?_⟩
  have h : t ^ 2 - t - 1 = 0 := by
    simpa only [IsRoot, eval_sub, eval_pow, eval_X, Polynomial.eval_one] using ht
  linear_combination h

theorem square_parameter (t : F) (ht : t ^ 2 = t + 1) :
    (t ^ 2) ^ 2 = t ^ 2 + 1 := by
  calc
    (t ^ 2) ^ 2 = (t + 1) ^ 2 := by rw [ht]
    _ = t ^ 2 + 1 := by rw [add_pow_char, one_pow]

omit [CharP F 2] in
theorem square_ne_self (t : F) (ht : t ^ 2 = t + 1) : t ^ 2 ≠ t := by
  intro h
  exact one_ne_zero (add_left_cancel (show t + (1 : F) = t + 0 by simpa using ht.symm.trans h))

omit [CharP F 2] in
theorem coefficient_ne_square (t : F) (ht : t ^ 2 = t + 1) (c : Fin 4)
    (hc : c = 2 ∨ c = 3) : coefficient t c ≠ coefficient (t ^ 2) c := by
  rcases hc with rfl | rfl
  · exact (square_ne_self t ht).symm
  · change t + 1 ≠ t ^ 2 + 1
    exact fun h => square_ne_self t ht (add_right_cancel h).symm

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
