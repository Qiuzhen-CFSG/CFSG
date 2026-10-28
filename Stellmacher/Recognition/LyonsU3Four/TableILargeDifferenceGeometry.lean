module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns

/-!
# Galois geometry of a large difference

Opposite sums and differences of the four difference columns have squared
norm sixteen. Galois symmetry pairs each of their entries with its negative,
so each entry has magnitude at most two. Thus a magnitude-two difference
forces the opposite difference in the same row to vanish.

The two predicates at the end distinguish the remaining possibilities: two
large differences in one row, or one large difference and two unit differences.
They are inputs to the contribution, congruence, and row-multiplicity arguments,
not assertions that a canonical table has already been obtained.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 377–378,
the opening reduction before Cases 1–4. The norm argument here proves the
opposite-entry assertion without making a choice of distinct Galois orbit rows.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

private theorem paired_bounds (f : I → ℤ) (hn : ∑ j, f j ^ 2 = 16)
    (hp : ∀ j, ∃ k, f k = -f j) (j : I) : -2 ≤ f j ∧ f j ≤ 2 := by
  classical
  obtain ⟨k, hk⟩ := hp j
  by_cases hzero : f j = 0
  · omega
  have hne : j ≠ k := by
    intro he
    subst k
    omega
  have hb : f j ^ 2 + f k ^ 2 ≤ 16 := by
    calc
      _ = ∑ x ∈ ({j, k} : Finset I), f x ^ 2 := by rw [Finset.sum_pair hne]
      _ ≤ ∑ x, f x ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = 16 := hn
  rw [hk] at hb
  constructor <;> nlinarith

/-- Index of the opposite side of the four-cycle. -/
def oppositeDifferenceIndex (i : Fin 4) : Fin 4 := ![2, 3, 0, 1] i

/-- The sum of two opposite difference columns has squared norm sixteen. -/
theorem opposite_add_sq_sum (h : d.Equation3_2) (i : Fin 4) :
    ∑ j, (d.adjacentDifference i j + d.adjacentDifference (oppositeDifferenceIndex i) j)^2
      = 16 := by
  simp_rw [add_sq]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [h.adjacentDifference_sq_sum d, h.adjacentDifference_sq_sum d]
  have hz := h.adjacentDifference_inner d i (oppositeDifferenceIndex i)
  have hz' : (∑ j, d.adjacentDifference i j * d.adjacentDifference (oppositeDifferenceIndex i) j) = 0 := by
    fin_cases i <;> simpa [columnInner, oppositeDifferenceIndex] using hz
  rw [hz']
  norm_num

/-- The difference of two opposite difference columns has squared norm sixteen. -/
theorem opposite_sub_sq_sum (h : d.Equation3_2) (i : Fin 4) :
    ∑ j, (d.adjacentDifference i j - d.adjacentDifference (oppositeDifferenceIndex i) j)^2
      = 16 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [h.adjacentDifference_sq_sum d, h.adjacentDifference_sq_sum d]
  have hz := h.adjacentDifference_inner d i (oppositeDifferenceIndex i)
  have hz' : (∑ j, d.adjacentDifference i j * d.adjacentDifference (oppositeDifferenceIndex i) j) = 0 := by
    fin_cases i <;> simpa [columnInner, oppositeDifferenceIndex] using hz
  rw [hz']
  norm_num

/-- Galois symmetry pairs opposite sums with their negatives. -/
theorem opposite_add_bounds (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (i : Fin 4) (j : I) :
    -2 ≤ d.adjacentDifference i j + d.adjacentDifference (oppositeDifferenceIndex i) j ∧
    d.adjacentDifference i j + d.adjacentDifference (oppositeDifferenceIndex i) j ≤ 2 := by
  apply paired_bounds _ (opposite_add_sq_sum d h i) _ j
  obtain ⟨σ, hσ⟩ := hg.adjacentDifference d
  intro k
  refine ⟨σ k, ?_⟩
  have hs := d.adjacentDifference_sum (σ k)
  simp [Fin.sum_univ_succ] at hs
  rw [hσ k i, hσ k (oppositeDifferenceIndex i)]
  fin_cases i <;> simp [oppositeDifferenceIndex] at * <;> omega

/-- Two Galois steps pair opposite differences with their negatives. -/
theorem opposite_sub_bounds (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (i : Fin 4) (j : I) :
    -2 ≤ d.adjacentDifference i j - d.adjacentDifference (oppositeDifferenceIndex i) j ∧
    d.adjacentDifference i j - d.adjacentDifference (oppositeDifferenceIndex i) j ≤ 2 := by
  apply paired_bounds _ (opposite_sub_sq_sum d h i) _ j
  obtain ⟨σ, hσ⟩ := hg.adjacentDifference d
  intro k
  refine ⟨σ (σ k), ?_⟩
  rw [hσ k i, hσ k (oppositeDifferenceIndex i), hσ (σ k), hσ (σ k)]
  fin_cases i <;> simp [oppositeDifferenceIndex]

/-- A magnitude-two difference has zero opposite difference. -/
theorem opposite_zero_of_large (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (i : Fin 4) (j : I) (hl : d.adjacentDifference i j ^ 2 = 4) :
    d.adjacentDifference (oppositeDifferenceIndex i) j = 0 := by
  have ha := opposite_add_bounds d h hg i j
  have hs := opposite_sub_bounds d h hg i j
  have he : d.adjacentDifference i j = 2 ∨ d.adjacentDifference i j = -2 := by
    have hb := h.adjacentDifference_bounds d i j
    rcases lt_trichotomy (d.adjacentDifference i j) 0 with hn | hz | hp
    · right; nlinarith
    · simp [hz] at hl
    · left; nlinarith
  rcases he with he | he <;> omega

omit [Fintype I] in
/-- A large entry may be moved into the first difference column by Galois symmetry. -/
theorem HasLargeDifference.at_zero (hl : d.HasLargeDifference) (hg : d.GaloisSymmetry) :
    ∃ j, d.adjacentDifference 0 j ^ 2 = 4 := by
  obtain ⟨σ, hσ⟩ := hg.adjacentDifference d
  obtain ⟨j, i, hi⟩ := hl
  fin_cases i
  · exact ⟨j, hi⟩
  · refine ⟨σ j, ?_⟩
    change d.adjacentDifference 1 j ^ 2 = 4 at hi
    rwa [hσ j 1] at hi
  · refine ⟨σ (σ j), ?_⟩
    change d.adjacentDifference 2 j ^ 2 = 4 at hi
    rw [hσ j 2] at hi
    change d.adjacentDifference 1 (σ j) ^ 2 = 4 at hi
    rwa [hσ (σ j) 1] at hi
  · refine ⟨σ (σ (σ j)), ?_⟩
    change d.adjacentDifference 3 j ^ 2 = 4 at hi
    rw [hσ j 3] at hi
    change d.adjacentDifference 2 (σ j) ^ 2 = 4 at hi
    rw [hσ (σ j) 2] at hi
    change d.adjacentDifference 1 (σ (σ j)) ^ 2 = 4 at hi
    rwa [hσ (σ (σ j)) 1] at hi

/-- The large entry shares its row with another large entry. -/
def HasPairedLargeDifferences : Prop :=
  ∃ (j : I) (ε : ℤ), ε ^ 2 = 1 ∧
    ((fun i => d.adjacentDifference i j) = (fun i => ε * ![2, -2, 0, 0] i) ∨
     (fun i => d.adjacentDifference i j) = (fun i => ε * ![2, 0, 0, -2] i))

/-- The large entry is the only large entry of its row. -/
def HasIsolatedLargeDifference : Prop :=
  ∃ (j : I) (ε : ℤ), ε ^ 2 = 1 ∧
    (fun i => d.adjacentDifference i j) = (fun i => ε * ![2, -1, 0, -1] i)


end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
