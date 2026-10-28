module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.Setup

/-!
# Separating the degree-four upper and Weyl matrix images

The image of the positive-root subgroup is upper unipotent. Weyl-word
matrices are supported on coordinate permutations, and multiplication
preserves this property. If such a matrix is also upper unipotent, its
nonzero diagonal forces the supporting permutation to be the identity.
This gives the intersection statement without faithfulness assumptions.

The permutation-support argument follows the degree-three proof in
`PSL3/UniversalProjection/Faithfulness/Bruhat/Separation.lean`.
Source: Steinberg, *Lectures on Chevalley Groups*, §§3 and 6, Theorem 8(b),
printed pp.32–33 and 69–71 (`refs/KGroup/GLS3/Chapter2St1.tex`).
The actual Bruhat kernel assembly consumes `upperWeylSeparation`.
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
open Theory.SpecificGroups.LinearHigher SteinbergWords
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {F : Type*} [Field F]

private def upperUnit (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j, j ≤ i → M i j = if i = j then 1 else 0

private theorem upperUnit_mul {A B : Matrix (Fin 4) (Fin 4) F}
    (ha : upperUnit A) (hb : upperUnit B) : upperUnit (A * B) := by
  intro i j hji
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [ha i i le_rfl, hb i j hji]
    simp
  · intro k _ hki
    by_cases hki' : k ≤ i
    · rw [ha i k hki', if_neg (Ne.symm hki), zero_mul]
    · have hjk : j < k := lt_of_le_of_lt hji (lt_of_not_ge hki')
      rw [hb k j hjk.le, if_neg (ne_of_gt hjk), mul_zero]
  · simp

private theorem upperUnit_generator {r : Root 4} (hr : r.val.1 < r.val.2) (a : F) :
    upperUnit (matrixMap (generator r a) : Matrix (Fin 4) (Fin 4) F) := by
  intro i j hji
  rw [matrixMap_generator]
  change (1 + Matrix.single r.val.1 r.val.2 a) i j = _
  have he : i ≠ r.val.1 ∨ j ≠ r.val.2 := by
    by_contra! h
    rcases h with ⟨rfl, rfl⟩
    exact (not_le_of_gt hr) hji
  rcases he with hi | hj
  · simp [Matrix.single, Matrix.one_apply, hi.symm]
  · simp [Matrix.single, Matrix.one_apply, hj.symm]

private theorem upper_matrix {u : SteinbergGroup 4 F} (hu : u ∈ upperSubgroup F) :
    upperUnit (matrixMap u : Matrix (Fin 4) (Fin 4) F) := by
  induction hu using Subgroup.closure_induction_left with
  | one => intro i j _; simp [Matrix.one_apply]
  | mul_left x hx y _ ih =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    simpa using upperUnit_mul (upperUnit_generator hr t) ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    rw [← generator_relations.neg]
    simpa using upperUnit_mul (upperUnit_generator hr (-t)) ih

private def supported (s : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ i j, i ≠ s j → M i j = 0

private theorem supported_mul {s t : Equiv.Perm (Fin 4)}
    {A B : Matrix (Fin 4) (Fin 4) F} (ha : supported s A) (hb : supported t B) :
    supported (s * t) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = t j
  · subst k
    rw [ha i (t j) hij, zero_mul]
  · rw [hb k j hk, mul_zero]

private theorem supported_weyl (r : Root 4) (t : Fˣ) :
    supported (Equiv.swap r.val.1 r.val.2)
      (matrixMap (weylWord generator r.val.1 r.val.2 r.property t) : Matrix (Fin 4) (Fin 4) F) := by
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

private theorem weyl_matrix {w : SteinbergGroup 4 F} (hw : w ∈ weylSubgroup F) :
    ∃ s : Equiv.Perm (Fin 4), supported s (matrixMap w : Matrix (Fin 4) (Fin 4) F) := by
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

/-- Upper-unipotent and monomial matrix images intersect only in the identity. -/
theorem upperWeylSeparation : UpperWeylSeparation F := by
  intro u w hu hw he
  have hu := upper_matrix hu
  obtain ⟨s, hs⟩ := weyl_matrix hw
  have hd (i : Fin 4) : (matrixMap w : Matrix (Fin 4) (Fin 4) F) i i = 1 := by
    rw [← he, hu i i le_rfl, if_pos rfl]
  have hsi (i : Fin 4) : s i = i := by
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

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
