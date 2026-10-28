module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Fin.Basic

/-!
# Uniqueness of reduced column bases

A reduced column basis has increasing pivot rows, an identity minor on those
rows, and zeros above each pivot. Equal column spaces have equal pivots: at the
first different pivot, expansion in the other basis would make a leading one
zero. Once pivots agree, their coordinate-recovery identities identify every
column. This elementary elimination argument also certifies independence.
-/

@[expose] public section
namespace Matrix
variable {n k : ℕ} {R : Type*} [Semiring R]

/-- The transpose of a reduced row echelon matrix with no zero rows. -/
structure ReducedColumnBasis (U : Matrix (Fin n) (Fin k) R) where
  pivot : Fin k → Fin n
  increasing : StrictMono pivot
  identity_minor : ∀ i j, U (pivot i) j = if i = j then 1 else 0
  leading_zero : ∀ i j, i < pivot j → U i j = 0

namespace ReducedColumnBasis
variable {U V : Matrix (Fin n) (Fin k) R}

/-- Pivot entries recover the coefficients of a column combination. -/
theorem coordinates (hU : ReducedColumnBasis U) (x : Fin k → R) (i : Fin k) :
    (U *ᵥ x) (hU.pivot i) = x i := by
  simp [mulVec, dotProduct, hU.identity_minor]

/-- An identity minor implies independence. -/
theorem injective (hU : ReducedColumnBasis U) : Function.Injective U.mulVec := by
  intro x y h
  funext i
  exact (hU.coordinates x i).symm.trans ((congrFun h (hU.pivot i)).trans
    (hU.coordinates y i))

variable [Nontrivial R]

private theorem pivot_le (hU : ReducedColumnBasis U) (hV : ReducedColumnBasis V)
    (h : Set.range U.mulVec = Set.range V.mulVec) (i : Fin k)
    (hprefix : ∀ j < i, hU.pivot j = hV.pivot j) : hV.pivot i ≤ hU.pivot i := by
  by_contra! hlt
  have hcol : (fun r => U r i) ∈ Set.range V.mulVec := by
    rw [← h]
    exact ⟨Pi.single i 1, by ext r; simp⟩
  obtain ⟨x, hx⟩ := hcol
  have hzero : (V *ᵥ x) (hU.pivot i) = 0 := by
    change ∑ j : Fin k, V (hU.pivot i) j * x j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j < i
    · have hxj : x j = 0 := by
        have hj := congrFun hx (hV.pivot j)
        rw [hV.coordinates, ← hprefix j hji, hU.identity_minor] at hj
        simpa [ne_of_lt hji] using hj
      rw [hxj, mul_zero]
    · rw [hV.leading_zero _ _ (hlt.trans_le (hV.increasing.monotone (le_of_not_gt hji))),
        zero_mul]
  have hi := congrFun hx (hU.pivot i)
  rw [hzero, hU.identity_minor, if_pos rfl] at hi
  exact zero_ne_one hi

/-- The column space determines the increasing pivot sequence. -/
theorem pivot_eq (hU : ReducedColumnBasis U) (hV : ReducedColumnBasis V)
    (h : Set.range U.mulVec = Set.range V.mulVec) : hU.pivot = hV.pivot := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    exact le_antisymm (hV.pivot_le hU h.symm i (fun j hj => (ih j hj).symm))
      (hU.pivot_le hV h i ih)

/-- Reduced column bases of the same space are equal. -/
theorem eq_of_range_eq (hU : ReducedColumnBasis U) (hV : ReducedColumnBasis V)
    (h : Set.range U.mulVec = Set.range V.mulVec) : U = V := by
  have hp := hU.pivot_eq hV h
  ext r i
  have hcol : (fun r => U r i) ∈ Set.range V.mulVec := by
    rw [← h]
    exact ⟨Pi.single i 1, by ext r; simp⟩
  obtain ⟨x, hx⟩ := hcol
  have hx' : x = Pi.single i 1 := by
    funext j
    have hj := congrFun hx (hV.pivot j)
    rw [hV.coordinates, ← hp, hU.identity_minor] at hj
    simpa [Pi.single_apply, eq_comm] using hj
  subst x
  simpa using (congrFun hx r).symm
end ReducedColumnBasis
end Matrix
