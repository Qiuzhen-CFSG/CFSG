module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.WellFounded

/-!
# Uniqueness of reduced row bases

A full row basis is reduced when its ordered pivot columns form an identity
minor and each row vanishes before its pivot. The leading column of any nonzero
vector in the row span is one of these pivots. Equal row spans therefore have
the same pivot set; ordering identifies their pivots and the identity minors
recover every row coordinate. Thus reduced row bases with equal spans coincide.

This is the usual uniqueness argument for reduced row echelon form, expressed
without a Gaussian-elimination algorithm. It supports exact orbit certificates
whose reduced bases have different pivot patterns.
-/

@[expose] public section

open Matrix

namespace Matrix
variable {m n : ℕ} {R : Type*} [Semiring R]

/-- A reduced row echelon matrix with no zero rows, together with its pivot columns. -/
structure IsReducedRowBasis (W : Matrix (Fin m) (Fin n) R) (p : Fin m → Fin n) : Prop where
  increasing : StrictMono p
  identity_minor : ∀ i j, W i (p j) = if i = j then 1 else 0
  zero_before : ∀ i j, j < p i → W i j = 0

/-- The pivot entries of a vector in the row span recover its coefficients. -/
lemma IsReducedRowBasis.coordinates {W : Matrix (Fin m) (Fin n) R}
    {p : Fin m → Fin n} (hW : IsReducedRowBasis W p) (c : Fin m → R) (i : Fin m) :
    (c ᵥ* W) (p i) = c i := by
  simp [Matrix.vecMul, dotProduct, hW.identity_minor]

/-- The leading column of a nonzero row-space vector is a pivot column. -/
lemma IsReducedRowBasis.leading_mem_range {W : Matrix (Fin m) (Fin n) R}
    {p : Fin m → Fin n} (hW : IsReducedRowBasis W p) {v : Fin n → R}
    (hv : v ∈ LinearMap.range W.vecMulLinear) {j : Fin n}
    (hne : v j ≠ 0) (hz : ∀ k, k < j → v k = 0) : j ∈ Set.range p := by
  obtain ⟨c, rfl⟩ := hv
  by_contra h
  apply hne
  change ∑ i, c i * W i j = 0
  apply Finset.sum_eq_zero
  intro i _
  have hij : p i ≠ j := fun hij => h ⟨i, hij⟩
  rcases lt_or_gt_of_ne hij with hij | hij
  · have hc : c i = 0 := (hW.coordinates c i).symm.trans (hz (p i) hij)
    rw [hc, zero_mul]
  · rw [hW.zero_before i j hij, mul_zero]

variable [Nontrivial R]

/-- Inclusion of row spaces implies inclusion of the pivot sets. -/
lemma IsReducedRowBasis.pivot_range_subset {W V : Matrix (Fin m) (Fin n) R}
    {p q : Fin m → Fin n} (hW : IsReducedRowBasis W p) (hV : IsReducedRowBasis V q)
    (h : LinearMap.range W.vecMulLinear ≤ LinearMap.range V.vecMulLinear) :
    Set.range p ⊆ Set.range q := by
  rintro j ⟨i, rfl⟩
  have hi : W i ∈ LinearMap.range W.vecMulLinear := by
    exact ⟨Pi.single i 1, Matrix.single_one_vecMul i W⟩
  apply hV.leading_mem_range (h hi)
  · simp [hW.identity_minor]
  · exact hW.zero_before i

/-- Reduced row bases are uniquely determined by their row spaces. -/
lemma IsReducedRowBasis.eq_of_range_eq {W V : Matrix (Fin m) (Fin n) R}
    {p q : Fin m → Fin n} (hW : IsReducedRowBasis W p) (hV : IsReducedRowBasis V q)
    (h : LinearMap.range W.vecMulLinear = LinearMap.range V.vecMulLinear) : W = V := by
  have hpq : p = q := (hW.increasing.range_inj hV.increasing).mp
    (Set.Subset.antisymm (hW.pivot_range_subset hV h.le)
      (hV.pivot_range_subset hW h.ge))
  subst q
  ext i j
  have hi : W i ∈ LinearMap.range V.vecMulLinear := by
    rw [← h]
    exact ⟨Pi.single i 1, Matrix.single_one_vecMul i W⟩
  obtain ⟨c, hc⟩ := hi
  have hci (k : Fin m) : c k = if i = k then 1 else 0 := by
    rw [← hV.coordinates c k]
    change (V.vecMulLinear c) (p k) = _
    rw [hc, hW.identity_minor]
  have hcs : c = Pi.single i 1 := by
    ext k
    simp [hci, Pi.single_apply, eq_comm]
  rw [hcs, Matrix.vecMulLinear_apply, Matrix.single_one_vecMul] at hc
  exact congrFun hc.symm j
/-- For reduced row bases, matrix distinctness suffices for row-space distinctness. -/
lemma range_vecMulLinear_injective_of_reduced {ι : Type*}
    (W : ι → Matrix (Fin m) (Fin n) R) (p : ι → Fin m → Fin n)
    (hW : ∀ i, IsReducedRowBasis (W i) (p i)) (hinj : Function.Injective W) :
    Function.Injective (fun i => LinearMap.range (W i).vecMulLinear) := by
  intro i j h
  exact hinj ((hW i).eq_of_range_eq (hW j) h)

end Matrix
