module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.TriangularSaturation.Coordinates

/-!
# Difference-root elimination in the signed Spin candidates

When a pivot row of the first diagonal block is a basis row, multiplication
by the corresponding same-sign difference root erases exactly one entry.
Six such operations reduce a four-dimensional unitriangular block to the
identity. Every operation is a point of the published root-generated subgroup.

Source: the concrete type-D instance of GLS3 Theorem 1.11.2 and Steinberg
(6.2)(a-b), `refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
open Triality.Standard.PositiveCoordinates
open scoped BigOperators
@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

lemma difference_mul_first (negative : Bool) (i j : Fin 4) (hij : i < j)
    (a : k) (g : Points k) (p q : Fin 4) :
    blockMatrix k negative (rootPoint k (signedRoot negative (difference i j hij)) a * g)
        (.inl p) (.inl q) =
      blockMatrix k negative g (.inl p) (.inl q) +
        if p = i then a * blockMatrix k negative g (.inl j) (.inl q) else 0 := by
  rw [map_mul, difference_matrix, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
  by_cases hp : p = i
  · subst p
    simp [Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne]
  · simp [Matrix.single_mul_apply_of_ne, hp]

/-- Once the pivot row is a basis row, a root operation erases exactly one entry
of the first diagonal block. -/
lemma erase_difference (negative : Bool) (g : Points k) (i j : Fin 4) (hij : i < j)
    (hrow : ∀ q, blockMatrix k negative g (.inl j) (.inl q) = if j = q then 1 else 0) :
    ∃ x : Points k, x ∈ unipotent k negative ∧
      ∀ p q, blockMatrix k negative (x * g) (.inl p) (.inl q) =
        if p = i ∧ q = j then 0 else blockMatrix k negative g (.inl p) (.inl q) := by
  let a := blockMatrix k negative g (.inl i) (.inl j)
  refine ⟨rootPoint k (signedRoot negative (difference i j hij)) a,
    difference_mem k negative i j hij a, ?_⟩
  intro p q
  rw [difference_mul_first, hrow]
  by_cases hp : p = i
  · subst p
    by_cases hq : q = j
    · subst q
      simp [a, CharTwo.add_self_eq_zero]
    · simp [hq, Ne.symm hq]
  · simp [hp]

/-- Six same-sign difference roots reduce the first unitriangular block to one. -/
lemma first_block_elimination (negative : Bool) (g : Points k)
    (hupper : ∀ i j : Fin 4, j < i → blockMatrix k negative g (.inl i) (.inl j) = 0)
    (hdiag : ∀ i : Fin 4, blockMatrix k negative g (.inl i) (.inl i) = 1) :
    ∃ x : Points k, x ∈ unipotent k negative ∧
      ∀ i j : Fin 4, blockMatrix k negative (x * g) (.inl i) (.inl j) =
        if i = j then 1 else 0 := by
  have hrow3 : ∀ q, blockMatrix k negative g (.inl 3) (.inl q) =
      if (3 : Fin 4) = q then 1 else 0 := by
    intro q
    fin_cases q <;> first | exact hdiag 3 | exact hupper 3 _ (by decide)
  obtain ⟨x23, hx23, h23⟩ := erase_difference k negative g 2 3 (by decide) hrow3
  have hrow3' : ∀ q, blockMatrix k negative (x23 * g) (.inl 3) (.inl q) =
      if (3 : Fin 4) = q then 1 else 0 := by simp [h23, hrow3]
  obtain ⟨x13, hx13, h13⟩ := erase_difference k negative (x23 * g) 1 3 (by decide) hrow3'
  have hrow2 : ∀ q, blockMatrix k negative (x13 * (x23 * g)) (.inl 2) (.inl q) =
      if (2 : Fin 4) = q then 1 else 0 := by
    intro q
    fin_cases q <;> simp [h13, h23, hdiag, hupper _ _ (show (0 : Fin 4) < 2 by decide),
      hupper _ _ (show (1 : Fin 4) < 2 by decide)]
  obtain ⟨x12, hx12, h12⟩ := erase_difference k negative (x13 * (x23 * g)) 1 2 (by decide) hrow2
  have hrow3'' : ∀ q, blockMatrix k negative (x12 * (x13 * (x23 * g))) (.inl 3) (.inl q) =
      if (3 : Fin 4) = q then 1 else 0 := by simp [h12, h13, h23, hrow3]
  obtain ⟨x03, hx03, h03⟩ := erase_difference k negative (x12 * (x13 * (x23 * g)))
    0 3 (by decide) hrow3''
  have hrow2' : ∀ q, blockMatrix k negative (x03 * (x12 * (x13 * (x23 * g)))) (.inl 2) (.inl q) =
      if (2 : Fin 4) = q then 1 else 0 := by simp [h03, h12, hrow2]
  obtain ⟨x02, hx02, h02⟩ := erase_difference k negative (x03 * (x12 * (x13 * (x23 * g))))
    0 2 (by decide) hrow2'
  have hrow1 : ∀ q, blockMatrix k negative (x02 * (x03 * (x12 * (x13 * (x23 * g)))))
      (.inl 1) (.inl q) = if (1 : Fin 4) = q then 1 else 0 := by
    intro q
    fin_cases q <;> simp [h02, h03, h12, h13, h23, hdiag,
      hupper _ _ (show (0 : Fin 4) < 1 by decide)]
  obtain ⟨x01, hx01, h01⟩ := erase_difference k negative
    (x02 * (x03 * (x12 * (x13 * (x23 * g))))) 0 1 (by decide) hrow1
  refine ⟨x01 * (x02 * (x03 * (x12 * (x13 * x23)))), ?_, ?_⟩
  · exact (unipotent k negative).toSubgroup.mul_mem hx01
      ((unipotent k negative).toSubgroup.mul_mem hx02
        ((unipotent k negative).toSubgroup.mul_mem hx03
          ((unipotent k negative).toSubgroup.mul_mem hx12
            ((unipotent k negative).toSubgroup.mul_mem hx13 hx23))))
  · intro i j
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    fin_cases i <;> fin_cases j <;>
      simp [h01, h02, h03, h12, h13, h23, hdiag, hupper _ _ (show (0 : Fin 4) < 1 by decide),
        hupper _ _ (show (0 : Fin 4) < 2 by decide), hupper _ _ (show (1 : Fin 4) < 2 by decide),
        hupper _ _ (show (0 : Fin 4) < 3 by decide), hupper _ _ (show (1 : Fin 4) < 3 by decide),
        hupper _ _ (show (2 : Fin 4) < 3 by decide)]

end Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
