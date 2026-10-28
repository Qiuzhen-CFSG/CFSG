module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterData

/-!
# The remaining columns of Janko's normalizer table

The five integral nonspecial columns are followed by the two classes of
elements of order five. Their two irrational entries are `t` and `1-t`,
where `t² = t + 1`. The displayed matrix is numerical data, not a character
construction. It is used to assemble separately constructed representations.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, p.11.
-/

open scoped BigOperators
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder

/-- Columns `1,a,c,c₁,bd` of the printed table. -/
@[expose] public def normalizerIntegralValues : Fin 12 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1], ![9, 1, 0, 0, 1], ![10, -2, 1, 1, 0],
    ![8, 0, -1, -1, 0], ![8, 0, -1, -1, 0], ![5, 1, 2, -1, -1],
    ![5, 1, -1, 2, -1], ![45, 1, 0, 0, -1], ![45, -3, 0, 0, 1],
    ![30, 2, -3, 0, 0], ![15, -1, 3, 0, -1], ![15, 3, 3, 0, 1]]

/-- Columns `μ,μ²`, with the two degree-eight entries interchanged. -/
@[expose] public def normalizerFiveValues (t : ℂ) : Fin 12 → Fin 2 → ℂ :=
  ![![1, 1], ![-1, -1], ![0, 0], ![t, 1-t], ![1-t, t],
    ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]

/-- The seven nonspecial columns, in order `1,a,c,c₁,bd,μ,μ²`. -/
@[expose] public def normalizerNonspecialValues (t : ℂ) (j : Fin 12) : Fin 7 → ℂ :=
  Fin.append (fun r => (normalizerIntegralValues j r : ℂ)) (normalizerFiveValues t j)

/-- The complete numerical table, with the five special columns first. -/
@[expose] public def normalizerFullValues (t : ℂ) (j : Fin 12) : Fin 12 → ℂ :=
  Fin.append (fun r => (normalizerCharacterValues j r : ℂ))
    (normalizerNonspecialValues t j)

/-- All five combinations cancel on the integral nonspecial columns. -/
public theorem normalizerIntegralValues_cancel : ∀ i r,
    (∑ j : Fin 12, exceptionalCoefficients i j * normalizerIntegralValues j r) = 0 := by
  decide +kernel

/-- Cancellation on the two fifth-order columns uses only the sum of their
two irrational entries. -/
public theorem normalizerFiveValues_cancel (t : ℂ) (i : Fin 5) (r : Fin 2) :
    (∑ j : Fin 12, (exceptionalCoefficients i j : ℂ) * normalizerFiveValues t j r) = 0 := by
  fin_cases i <;> fin_cases r <;>
    simp [Fin.sum_univ_succ, exceptionalCoefficients, normalizerFiveValues]

/-- Every nonspecial column is annihilated by the five coefficient vectors. -/
public theorem normalizerNonspecialValues_cancel (t : ℂ) (i : Fin 5) (r : Fin 7) :
    (∑ j : Fin 12, (exceptionalCoefficients i j : ℂ) *
      normalizerNonspecialValues t j r) = 0 := by
  refine Fin.addCases (m := 5) (n := 2) (fun r => ?_) (fun r => ?_) r
  · simp only [normalizerNonspecialValues, Fin.append_left, ← Int.cast_mul, ← Int.cast_sum,
      normalizerIntegralValues_cancel, Int.cast_zero]
  · simpa only [normalizerNonspecialValues, Fin.append_right] using
      normalizerFiveValues_cancel t i r

/-- The five induced rows do not involve the fifth-root parameter. -/
public theorem normalizerFullValues_induced (t : ℂ) (j : Fin 5) (r : Fin 12) :
    normalizerFullValues t (Fin.natAdd 7 j) r =
      normalizerFullValues 0 (Fin.natAdd 7 j) r := by
  fin_cases j <;> fin_cases r <;>
    simp [normalizerFullValues, normalizerNonspecialValues, normalizerFiveValues, Fin.append]

private theorem integral_rows_distinguish : ∀ i j : Fin 12,
    (∀ r, normalizerIntegralValues i r = normalizerIntegralValues j r) →
      i = j ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
  decide +kernel

/-- The complete rows are distinct; the fifth-order column separates the
two degree-eight rows, which agree on every integral column. -/
public theorem normalizerFullValues_injective (t : ℂ) (ht : t ^ 2 = t + 1) :
    Function.Injective (normalizerFullValues t) := by
  intro i j hij
  have hi : ∀ r, normalizerIntegralValues i r = normalizerIntegralValues j r := by
    intro r
    have h := congrFun hij (Fin.natAdd 5 (Fin.castAdd 2 r))
    simp only [normalizerFullValues, Fin.append_right, normalizerNonspecialValues,
      Fin.append_left] at h
    exact_mod_cast h
  have hne : t ≠ 1 - t := by
    intro h
    have ht' : t = 1 / 2 := by linear_combination (1 / 2 : ℂ) * h
    norm_num [ht'] at ht
  rcases integral_rows_distinguish i j hi with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · have h := congrFun hij 10
    exact (hne h).elim
  · have h := congrFun hij 10
    exact (hne h.symm).elim

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
