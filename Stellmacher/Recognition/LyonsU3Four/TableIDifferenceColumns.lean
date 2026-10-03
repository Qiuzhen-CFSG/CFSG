module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

/-!
# Difference columns for the Table I enumeration

The four successive differences of the rotating involution columns have the
Gram matrix of a square: norm eight, neighboring inner product minus four,
and opposite inner product zero. Consequently every entry has magnitude at
most two. This gives the first division in Lyons's enumeration. The remaining
divisions distinguish consecutive equal unit differences and the sparse
opposite pattern `(1, 0, -1, 0)`.

These are reductions of the enumeration, not an assertion of exhaustiveness
of the canonical catalogue. Source: R. Lyons, *A Characterization of the Group
U₃(4)* (1972), pp. 377–380, Cases 1–8.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators

variable {I : Type*} (d : GeneralizedDecompositionData I)

/-- Lyons's four columns `₁A,…,₄A`, indexed here starting at zero. -/
def adjacentDifference (i : Fin 4) (j : I) : ℤ :=
  d.iDz (![1, 2, 3, 4] i) j - d.iDz (![2, 3, 4, 1] i) j

theorem adjacentDifference_sum (j : I) :
    ∑ i, d.adjacentDifference i j = 0 := by
  simp [adjacentDifference, Fin.sum_univ_succ]
  ring

/-- The Galois permutation rotates the four difference columns. -/
theorem GaloisSymmetry.adjacentDifference (h : d.GaloisSymmetry) :
    ∃ σ : Equiv.Perm I, ∀ j i,
      d.adjacentDifference i j =
        d.adjacentDifference (![3, 0, 1, 2] i) (σ j) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, ?_⟩
  intro j i
  unfold GeneralizedDecompositionData.adjacentDifference
  rw [(hσ j).2, (hσ j).2]
  fin_cases i <;> rfl

/-- The large-difference branch, corresponding to source Cases 1–4. -/
def HasLargeDifference : Prop :=
  ∃ j i, d.adjacentDifference i j ^ 2 = 4

/-- The configuration starting source Case 5. Its rotations are supplied by
the Galois symmetry when needed in the enumeration. -/
def HasConsecutiveUnitDifferences : Prop :=
  ∃ j, d.adjacentDifference 0 j * d.adjacentDifference 1 j = 1

/-- The opposite sparse configuration used in source Cases 7–8. -/
def HasOppositeUnitDifferences : Prop :=
  ∃ j, (fun i => d.adjacentDifference i j) = ![1, 0, -1, 0] ∨
    (fun i => d.adjacentDifference i j) = ![-1, 0, 1, 0]

variable [Fintype I]

/-- Bilinearity of the Gram identities, for arbitrary column differences. -/
theorem Equation3_2.difference_inner (h : d.Equation3_2) (a b c e : Fin 5) :
    columnInner (fun j => d.iDz a j - d.iDz b j)
      (fun j => d.iDz c j - d.iDz e j) =
      4 * ((if a = c then 1 else 0) - (if a = e then 1 else 0) -
        (if b = c then 1 else 0) + (if b = e then 1 else 0)) := by
  simp only [columnInner, sub_mul, mul_sub, Finset.sum_sub_distrib]
  change (columnInner (d.iDz a) (d.iDz c) - columnInner (d.iDz b) (d.iDz c)) -
    (columnInner (d.iDz a) (d.iDz e) - columnInner (d.iDz b) (d.iDz e)) = _
  rw [h.zz, h.zz, h.zz, h.zz]
  ring

theorem Equation3_2.adjacentDifference_inner (h : d.Equation3_2) (i k : Fin 4) :
    columnInner (d.adjacentDifference i) (d.adjacentDifference k) =
      (![![8, -4, 0, -4], ![-4, 8, -4, 0],
         ![0, -4, 8, -4], ![-4, 0, -4, 8]] : Fin 4 → Fin 4 → ℤ) i k := by
  unfold adjacentDifference
  rw [h.difference_inner]
  fin_cases i <;> fin_cases k <;> decide

theorem Equation3_2.adjacentDifference_sq_sum (h : d.Equation3_2) (i : Fin 4) :
    ∑ j, d.adjacentDifference i j ^ 2 = 8 := by
  have hi := h.adjacentDifference_inner d i i
  fin_cases i <;> simpa [columnInner, pow_two] using hi

theorem Equation3_2.adjacentDifference_bounds (h : d.Equation3_2)
    (i : Fin 4) (j : I) :
    -2 ≤ d.adjacentDifference i j ∧ d.adjacentDifference i j ≤ 2 := by
  have hb : d.adjacentDifference i j ^ 2 ≤ 8 := by
    calc
      _ ≤ ∑ k, d.adjacentDifference i k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ = 8 := h.adjacentDifference_sq_sum d i
  constructor <;> nlinarith

/-- Outside the first branch all four difference columns have unit bounds. -/
theorem Equation3_2.unit_bounds_of_not_large (h : d.Equation3_2)
    (hn : ¬ d.HasLargeDifference) (i : Fin 4) (j : I) :
    -1 ≤ d.adjacentDifference i j ∧ d.adjacentDifference i j ≤ 1 := by
  have hb := h.adjacentDifference_bounds d i j
  have he : d.adjacentDifference i j ^ 2 ≠ 4 := fun he => hn ⟨j, i, he⟩
  have hpos : d.adjacentDifference i j ≠ 2 := by
    intro hp
    exact he (by rw [hp]; norm_num)
  have hneg : d.adjacentDifference i j ≠ -2 := by
    intro hp
    exact he (by rw [hp]; norm_num)
  omega

omit [Fintype I] in
/-- The four independent branches of the source enumeration. Each branch
still has to identify the rows with an explicit canonical matrix. -/
theorem tableI_difference_cases :
    d.HasLargeDifference ∨
    (¬ d.HasLargeDifference ∧ d.HasConsecutiveUnitDifferences) ∨
    (¬ d.HasLargeDifference ∧ ¬ d.HasConsecutiveUnitDifferences ∧
      ¬ d.HasOppositeUnitDifferences) ∨
    (¬ d.HasLargeDifference ∧ ¬ d.HasConsecutiveUnitDifferences ∧
      d.HasOppositeUnitDifferences) := by
  by_cases hl : d.HasLargeDifference
  · exact Or.inl hl
  by_cases hc : d.HasConsecutiveUnitDifferences
  · exact Or.inr (Or.inl ⟨hl, hc⟩)
  by_cases ho : d.HasOppositeUnitDifferences
  · exact Or.inr (Or.inr (Or.inr ⟨hl, hc, ho⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hl, hc, ho⟩))

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
