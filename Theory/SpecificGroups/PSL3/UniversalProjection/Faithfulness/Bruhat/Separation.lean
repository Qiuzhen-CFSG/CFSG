module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Setup

/-!
# Separating positive and Weyl matrix images in degree three

Products of positive root matrices have the upper-unipotent form with three
free entries. Weyl word matrices are supported on coordinate permutations;
their products retain this support property. If such a matrix also has
all diagonal entries one, its supporting permutation fixes every coordinate,
and the matrix is the identity.

This argument concerns the literal map to SL₃. It assumes neither torus
multiplicativity nor faithfulness on either of the two generated subgroups.
It supplies the matrix separation used in the degree-three Bruhat kernel
argument of Steinberg, *Lectures on Chevalley Groups*, §3 and §6,
Theorem 8(b), printed pp.32–33 and 69–71
(`refs/KGroup/GLS3/Chapter2St1.tex`); GLS3 §2.9, printed pp.97–98.
-/

@[expose] public section

open Theory.SpecificGroups.LinearHigher SteinbergWords
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Matrix.PSL3.UniversalProjection.Faithfulness
variable {F : Type*} [Field F]

private def upperMatrix (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, b; 0, 1, c; 0, 0, 1]

private theorem upperMatrix_mul (a b c d e f : F) :
    upperMatrix a b c * upperMatrix d e f =
      upperMatrix (a + d) (b + a * f + e) (c + f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem upper_generator_matrix {r : Root 3} (hr : r.val.1 < r.val.2) (t : F) :
    ∃ a b c, (matrixMap (generator r t) : Matrix (Fin 3) (Fin 3) F) = upperMatrix a b c := by
  obtain ⟨⟨i, j⟩, hij⟩ := r
  fin_cases i <;> fin_cases j <;> try {simp_all; done}
  · refine ⟨t, 0, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixMap_generator, matrixRoot, transvection_coe, upperMatrix, Matrix.single]
  · refine ⟨0, t, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixMap_generator, matrixRoot, transvection_coe, upperMatrix, Matrix.single]
  · refine ⟨0, 0, t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixMap_generator, matrixRoot, transvection_coe, upperMatrix, Matrix.single]

private theorem upper_matrix {u : SteinbergGroup 3 F} (hu : u ∈ upperSubgroup F) :
    ∃ a b c, (matrixMap u : Matrix (Fin 3) (Fin 3) F) = upperMatrix a b c := by
  have hm {u v : SteinbergGroup 3 F}
      (hu : ∃ a b c, (matrixMap u : Matrix (Fin 3) (Fin 3) F) = upperMatrix a b c)
      (hv : ∃ a b c, (matrixMap v : Matrix (Fin 3) (Fin 3) F) = upperMatrix a b c) :
      ∃ a b c, (matrixMap (u * v) : Matrix (Fin 3) (Fin 3) F) = upperMatrix a b c := by
    obtain ⟨a, b, c, ha⟩ := hu
    obtain ⟨d, e, f, hd⟩ := hv
    exact ⟨a + d, b + a * f + e, c + f, by
      rw [map_mul, coe_mul, ha, hd, upperMatrix_mul]⟩
  induction hu using Subgroup.closure_induction_left with
  | one =>
    refine ⟨0, 0, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperMatrix]
  | mul_left x hx y _ ih =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact hm (upper_generator_matrix hr t) ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    rw [← generator_relations.neg]
    exact hm (upper_generator_matrix hr (-t)) ih

private def supported (s : Equiv.Perm (Fin 3)) (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ i j, i ≠ s j → M i j = 0

private theorem supported_mul {s t : Equiv.Perm (Fin 3)}
    {A B : Matrix (Fin 3) (Fin 3) F} (ha : supported s A) (hb : supported t B) :
    supported (s * t) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = t j
  · subst k
    rw [ha i (t j) hij, zero_mul]
  · rw [hb k j hk, mul_zero]

private theorem supported_weyl (r : Root 3) (t : Fˣ) :
    supported (Equiv.swap r.val.1 r.val.2)
      (matrixMap (weylWord generator r.val.1 r.val.2 r.property t) : Matrix (Fin 3) (Fin 3) F) := by
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

private theorem weyl_matrix {w : SteinbergGroup 3 F} (hw : w ∈ weylSubgroup F) :
    ∃ s : Equiv.Perm (Fin 3), supported s (matrixMap w : Matrix (Fin 3) (Fin 3) F) := by
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨1, by intro i j hij; simpa using Matrix.one_apply_ne (show i ≠ j from hij)⟩
  | mul_left x hx y _ ih =>
    obtain ⟨r, t, rfl⟩ := hx
    obtain ⟨s, hs⟩ := ih
    exact ⟨Equiv.swap r.val.1 r.val.2 * s, by
      simpa using supported_mul (supported_weyl r t) hs⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨r, t, rfl⟩ := hx
    rw [weylWord_inv generator_relations]
    obtain ⟨s, hs⟩ := ih
    exact ⟨Equiv.swap r.val.1 r.val.2 * s, by
      simpa using supported_mul (supported_weyl r (-t)) hs⟩

/-- The positive-root and Weyl matrix images intersect only in the identity
of SL₃, without any presentation-faithfulness assumption. -/
theorem upperWeylSeparation : UpperWeylSeparation F := by
  intro u w hu hw he
  obtain ⟨a, b, c, hu⟩ := upper_matrix hu
  obtain ⟨s, hs⟩ := weyl_matrix hw
  have hd (i : Fin 3) : (matrixMap w : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    rw [← he, hu]
    fin_cases i <;> rfl
  have hsi (i : Fin 3) : s i = i := by
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
end Matrix.PSL3.UniversalProjection.Faithfulness
