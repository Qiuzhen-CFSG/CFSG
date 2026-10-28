module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Commutator generation of the plane-local radical

For a finite field of order `2 ^ n`, with `n > 1`, the actual plane-local
radical satisfies `[radical, planeLocal] = radical`.

In symmetric-matrix coordinates, conjugation by an upper unipotent of
parameter `s` sends the second diagonal coordinate `b` to a matrix whose
difference from the original has coordinates `(s²b, sb, 0)`. Subtracting
the differences for parameters `t` and `1`, with inputs `b` and `tb`, gives
`((t²-t)b, 0, 0)`. Choose `t ≠ 0, 1` using the field cardinality. Lower
unipotents give the second diagonal coordinate, and the upper-unipotent
identity then gives the off-diagonal coordinate. All differences are
commutators of explicit Levi lifts with actual shears.

This is the radical-generation calculation needed for the nonbinary
Sp₄ block assertion in Aschbacher--Smith F.1.12(I)(2), printed pp.262–264
of the combined manuscript of 1 March 2004. The central quotient and the
remaining block assertions are separate results.
-/

open Matrix
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.Plane
noncomputable section
variable {F : Type*} [Field F]

private theorem shear_neg' (B : symmetricMatrices F) : shear (-B) = (shear B)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← shear_add, neg_add_cancel, shear_zero]

private def commutatorCoordinates : AddSubgroup (symmetricMatrices F) where
  carrier := {B | shear B ∈ ⁅radical (F := F), (⊤ : Subgroup (planeLocal (F := F)))⁆}
  zero_mem' := by simp
  add_mem' hB hC := by simpa only [Set.mem_ofPred_eq, shear_add] using Subgroup.mul_mem _ hB hC
  neg_mem' hB := by simpa only [Set.mem_ofPred_eq, shear_neg'] using Subgroup.inv_mem _ hB

private theorem congruence_sub_mem (A : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) : congruence A B - B ∈ commutatorCoordinates := by
  change shear (congruence A B - B) ∈ ⁅radical (F := F), (⊤ : Subgroup (planeLocal (F := F)))⁆
  rw [sub_eq_add_neg, shear_add, shear_neg', ← quotientMap_levi A,
    ← conjugate_shear]
  change ⁅levi A, shear B⁆ ∈ ⁅radical (F := F), (⊤ : Subgroup (planeLocal (F := F)))⁆
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (quotientMap_shear B)

private def sym (a b c : F) : symmetricMatrices F :=
  ⟨!![a, b; b, c], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩

private def upper (s : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

private def lower (s : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

private theorem upper_diff (s b : F) :
    congruence (upper s) (sym 0 0 b) - sym 0 0 b = sym (s * s * b) (s * b) 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [congruence, upper, sym, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem lower_diff (s b : F) :
    congruence (lower s) (sym b 0 0) - sym b 0 0 = sym 0 (s * b) (s * s * b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [congruence, lower, sym, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem diag_first_mem (t : F) (ht : t * t - t ≠ 0) (a : F) :
    sym a 0 0 ∈ commutatorCoordinates := by
  let b := a / (t * t - t)
  -- The off-diagonal terms cancel, leaving `(t²-t)b` on the diagonal.
  have h1 := congruence_sub_mem (upper t) (sym 0 0 b)
  have h2 := congruence_sub_mem (upper 1) (sym 0 0 (t * b))
  rw [upper_diff] at h1 h2
  have h := (commutatorCoordinates (F := F)).sub_mem h1 h2
  have he : sym (t * t * b) (t * b) 0 - sym (1 * 1 * (t * b)) (1 * (t * b)) 0 = sym a 0 0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym, b]
    rw [← sub_mul, mul_div_cancel₀ _ ht]
  rwa [he] at h

private theorem diag_second_mem (t : F) (ht : t * t - t ≠ 0) (a : F) :
    sym 0 0 a ∈ commutatorCoordinates := by
  let b := a / (t * t - t)
  have h1 := congruence_sub_mem (lower t) (sym b 0 0)
  have h2 := congruence_sub_mem (lower 1) (sym (t * b) 0 0)
  rw [lower_diff] at h1 h2
  have h := (commutatorCoordinates (F := F)).sub_mem h1 h2
  have he : sym 0 (t * b) (t * t * b) - sym 0 (1 * (t * b)) (1 * 1 * (t * b)) = sym 0 0 a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym, b]
    rw [← sub_mul, mul_div_cancel₀ _ ht]
  rwa [he] at h

private theorem off_diagonal_mem (t : F) (ht : t * t - t ≠ 0) (a : F) :
    sym 0 a 0 ∈ commutatorCoordinates := by
  have h := (commutatorCoordinates (F := F)).sub_mem
    (congruence_sub_mem (upper 1) (sym 0 0 a)) (diag_first_mem t ht a)
  rw [upper_diff] at h
  have he : sym (1 * 1 * a) (1 * a) 0 - sym a 0 0 = sym 0 a 0 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym]
  rwa [he] at h

private theorem all_coordinates_mem (t : F) (ht : t * t - t ≠ 0)
    (B : symmetricMatrices F) : B ∈ commutatorCoordinates := by
  have h := (commutatorCoordinates (F := F)).add_mem
    ((commutatorCoordinates (F := F)).add_mem
      (diag_first_mem t ht (B.val 0 0)) (off_diagonal_mem t ht (B.val 0 1)))
    (diag_second_mem t ht (B.val 1 1))
  have he : sym (B.val 0 0) 0 0 + sym 0 (B.val 0 1) 0 + sym 0 0 (B.val 1 1) = B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym]
    exact congrFun (congrFun B.property 1) 0
  rwa [he] at h

private theorem exists_parameter [Finite F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
  let := Fintype.ofFinite F
  apply ENat.exists_ne_ne_of_three_le
  rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  exact_mod_cast (show 3 ≤ 2 ^ n by
    have h : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
    omega)

/-- The radical of the actual plane local group is generated by its commutators. -/
public theorem radical_commutator_eq [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ⁅radical (F := F), (⊤ : Subgroup (planeLocal (F := F)))⁆ = radical := by
  obtain ⟨t, ht0, ht1⟩ := exists_parameter hcard hn
  have ht : t * t - t ≠ 0 := by
    rw [← mul_sub_one]
    exact mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
  apply le_antisymm (Subgroup.commutator_le_left _ _)
  intro q hq
  have h := all_coordinates_mem t ht (radicalEquiv ⟨q, hq⟩).toAdd
  change shear (radicalEquiv ⟨q, hq⟩).toAdd ∈ ⁅radical (F := F), (⊤ : Subgroup (planeLocal (F := F)))⁆ at h
  have he : shear (radicalEquiv ⟨q, hq⟩).toAdd = q :=
    congrArg Subtype.val (radicalEquiv.symm_apply_apply ⟨q, hq⟩)
  rwa [he] at h

end
end Theory.SpecificGroups.SymplecticFour.Plane
