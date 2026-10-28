module

public import Theory.SpecificGroups.LinearHigher.PresentationFaithfulness.Setup
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Separation of positive and Weyl matrix images

The literal positive-root subgroup maps to upper-unipotent matrices.
The literal Weyl subgroup maps to matrices supported on coordinate
permutations. If these images agree, the diagonal entries force every
coordinate to be fixed, so the common matrix is the identity.

This argument is uniform in the dimension and field and does not assume
faithfulness on either subgroup. It supplies the matrix separation used
by `LinearHigher.matrixMap_injective_of_bruhat`.

Source: Steinberg, *Lectures on Chevalley Groups*, §§3 and 6, Theorem
8(b), printed pp.32–33 and 69–71 (`refs/KGroup/GLS3/Chapter2St1.tex`).
The permutation-support proof follows the checked degree-three argument
in `PSL3/UniversalProjection/Faithfulness/Bruhat/Separation.lean`.
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher.PresentationFaithfulness
open SteinbergWords Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {n : ℕ} {F : Type*} [Field F]

private def UpperMatrix (M : Matrix (Fin n) (Fin n) F) : Prop :=
  M.BlockTriangular id ∧ ∀ i, M i i = 1

private theorem upperMatrix_mul {M N : Matrix (Fin n) (Fin n) F}
    (hM : UpperMatrix M) (hN : UpperMatrix N) : UpperMatrix (M * N) := by
  refine ⟨hM.1.mul hN.1, ?_⟩
  intro i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hM.2, hN.2, mul_one]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hM.1 hj, zero_mul]
    · rw [hN.1 hj, mul_zero]
  · simp

private theorem upperMatrix_generator {r : Root n} (hr : r.val.1 < r.val.2) (a : F) :
    UpperMatrix (matrixMap (generator r a) : Matrix (Fin n) (Fin n) F) := by
  simp only [matrixMap_generator, matrixRoot, transvection_coe]
  refine ⟨Matrix.blockTriangular_transvection (b := id) hr.le a, ?_⟩
  intro i
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  rw [Matrix.single_apply_of_ne, add_zero]
  rintro ⟨rfl, h⟩
  exact r.property h.symm

/-- Every diagonal entry of a positive-root word is one. -/
theorem matrixMap_upper_diagonal {u : SteinbergGroup n F} (hu : u ∈ upperSubgroup n F)
    (i : Fin n) : (matrixMap u : Matrix (Fin n) (Fin n) F) i i = 1 := by
  have h : UpperMatrix (matrixMap u : Matrix (Fin n) (Fin n) F) := by
    induction hu using Subgroup.closure_induction_left with
    | one => exact ⟨Matrix.blockTriangular_one, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨r, a, hr, rfl⟩ := hx
      simpa only [map_mul, coe_mul] using upperMatrix_mul (upperMatrix_generator hr a) ih
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨r, a, hr, rfl⟩ := hx
      rw [← generator_relations.neg]
      simpa only [map_mul, coe_mul] using upperMatrix_mul (upperMatrix_generator hr (-a)) ih
  exact h.2 i

private def Supported (s : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, i ≠ s j → M i j = 0

private theorem supported_mul {s t : Equiv.Perm (Fin n)}
    {A B : Matrix (Fin n) (Fin n) F} (ha : Supported s A) (hb : Supported t B) :
    Supported (s * t) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = t j
  · subst k
    rw [ha i (t j) hij, zero_mul]
  · rw [hb k j hk, mul_zero]

private theorem supported_weyl (r : Root n) (t : Fˣ) :
    Supported (Equiv.swap r.val.1 r.val.2)
      (matrixMap (weylWord generator r.val.1 r.val.2 r.property t) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨⟨i, j⟩, hij⟩ := r
  intro k l hkl
  simp only [weylWord, map_mul, matrixMap_generator, coe_mul, matrixRoot]
  change (Matrix.transvection i j (t : F) *
    Matrix.transvection j i (-((t⁻¹ : Fˣ) : F)) * Matrix.transvection i j (t : F)) k l = 0
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j
  all_goals try {subst_vars; contradiction}
  all_goals subst_vars
  all_goals simp_all only [Matrix.mul_assoc, Matrix.transvection_mul_apply_same,
    Matrix.transvection_mul_apply_of_ne, ne_eq, not_false_eq_true]
  all_goals simp_all [Equiv.swap_apply_def, Matrix.transvection, Matrix.single,
    Matrix.one_apply, eq_comm]

/-- Every Weyl word has matrix support on a coordinate permutation. -/
theorem matrixMap_weyl_supported {w : SteinbergGroup n F} (hw : w ∈ weylSubgroup n F) :
    ∃ s : Equiv.Perm (Fin n), ∀ i j, i ≠ s j →
      (matrixMap w : Matrix (Fin n) (Fin n) F) i j = 0 := by
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨1, by intro i j hij; simpa using Matrix.one_apply_ne (show i ≠ j from hij)⟩
  | mul_left x hx y _ ih =>
    obtain ⟨r, t, rfl⟩ := hx
    obtain ⟨s, hs⟩ := ih
    exact ⟨Equiv.swap r.val.1 r.val.2 * s, by
      simpa [Supported] using supported_mul (supported_weyl r t) hs⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨r, t, rfl⟩ := hx
    rw [weylWord_inv generator_relations]
    obtain ⟨s, hs⟩ := ih
    exact ⟨Equiv.swap r.val.1 r.val.2 * s, by
      simpa [Supported] using supported_mul (supported_weyl r (-t)) hs⟩

/-- The positive and monomial matrix images intersect only at the identity. -/
theorem matrixMap_eq_one_of_upper_of_weyl {u w : SteinbergGroup n F}
    (hu : u ∈ upperSubgroup n F) (hw : w ∈ weylSubgroup n F)
    (he : matrixMap u = matrixMap w) : matrixMap w = 1 := by
  obtain ⟨s, hs⟩ := matrixMap_weyl_supported hw
  have hd (i : Fin n) : (matrixMap w : Matrix (Fin n) (Fin n) F) i i = 1 := by
    rw [← he]
    exact matrixMap_upper_diagonal hu i
  have hsi (i : Fin n) : s i = i := by
    by_contra hn
    have hz := hs i i (Ne.symm hn)
    rw [hd] at hz
    exact one_ne_zero hz
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using hd i
  · simpa [Matrix.one_apply, hij] using hs i j (by simpa [hsi] using hij)

end Theory.SpecificGroups.LinearHigher.PresentationFaithfulness
