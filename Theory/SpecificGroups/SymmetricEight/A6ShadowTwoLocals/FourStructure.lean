module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.FourStructure.Maximality

/-!
# Characteristic two of the two-four-point-block stabilizer

The double transpositions on each four-point block give a subgroup V₄ × V₄.
Its small multiplication table proves that it is a two-group. Conjugation by
the block stabilizer permutes the double transpositions on the two blocks,
proving relative normality. A permutation centralizing this subgroup fixes
each block setwise and is determined by its images of 0 and 4; these images
identify it with a member of V₄ × V₄.

Adjoining the central C₂ gives a normal two-subgroup of `fourOvergroup` whose
ambient centralizer lies in itself. Its inclusion in the intrinsic two-core
therefore proves the required core-centralizer bound. The imported maximality
result completes the two properties of this standard overgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the two maximal proper 2-locals used in the proof of
Lemma 2.5.26, printed p.569. The finite checks below concern explicit point
permutations and their multiplication, with proofs checked by the kernel.
-/

public section

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup Equiv

private def leftKlein : Fin 4 → S8 :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

private def rightKlein : Fin 4 → S8 :=
  ![1, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7, swap 4 7 * swap 5 6]

private def kleinPerm (a b : Fin 4) : S8 := leftKlein a * rightKlein b

private theorem klein_mul_table : ∀ a b c d : Fin 4,
    ∃ e f : Fin 4, kleinPerm a b * kleinPerm c d = kleinPerm e f := by decide

private theorem klein_square : ∀ a b : Fin 4, kleinPerm a b * kleinPerm a b = 1 := by decide

private def kleinGroup : Subgroup S8 where
  carrier := {g | ∃ a b, g = kleinPerm a b}
  one_mem' := ⟨0, 0, rfl⟩
  mul_mem' := by
    rintro g h ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact klein_mul_table a b c d
  inv_mem' := by
    rintro g ⟨a, b, rfl⟩
    exact ⟨a, b, inv_eq_of_mul_eq_one_right (klein_square a b)⟩

private theorem klein_le_four : kleinGroup ≤ fourStabilizer := by
  have ht : ∀ a b : Fin 4, kleinPerm a b ∈ fourStabilizer := by decide
  rintro g ⟨a, b, rfl⟩
  exact ht a b

private theorem klein_pgroup : IsPGroup 2 kleinGroup := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨a, b, he⟩ := g.property
  change (g : S8) ^ (2 ^ 1) = 1
  simpa only [he, pow_one, pow_two] using klein_square a b

private theorem double_swap_mem (a b c d : Fin 8)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : a.val / 4 = b.val / 4) (h₂ : a.val / 4 = c.val / 4)
    (h₃ : a.val / 4 = d.val / 4) : swap a b * swap c d ∈ kleinGroup := by
  have ht : ∀ a b c d : Fin 8,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      a.val / 4 = b.val / 4 → a.val / 4 = c.val / 4 → a.val / 4 = d.val / 4 →
      ∃ e f : Fin 4, swap a b * swap c d = kleinPerm e f := by
    decide
  exact ht a b c d hab hac had hbc hbd hcd h₁ h₂ h₃

private theorem conj_double_swap_mem (g : S8) (hg : g ∈ fourStabilizer)
    (a b c d : Fin 8)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : a.val / 4 = b.val / 4) (h₂ : a.val / 4 = c.val / 4)
    (h₃ : a.val / 4 = d.val / 4) :
    g * (swap a b * swap c d) * g⁻¹ ∈ kleinGroup := by
  have he : g * (swap a b * swap c d) * g⁻¹ =
      swap (g a) (g b) * swap (g c) (g d) := by
    calc
      _ = (g * swap a b * g⁻¹) * (g * swap c d * g⁻¹) := by simp [mul_assoc]
      _ = _ := by
        rw [Equiv.mul_swap_eq_swap_mul g a b, Equiv.mul_swap_eq_swap_mul g c d]
        simp
  rw [he]
  exact double_swap_mem _ _ _ _ (g.injective.ne hab) (g.injective.ne hac)
    (g.injective.ne had) (g.injective.ne hbc) (g.injective.ne hbd)
    (g.injective.ne hcd) ((hg a b).mpr h₁) ((hg a c).mpr h₂) ((hg a d).mpr h₃)

private theorem four_normalizes_klein : fourStabilizer ≤ normalizer (kleinGroup : Set S8) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg n hn
  obtain ⟨a, b, rfl⟩ := hn
  have hl : g * leftKlein a * g⁻¹ ∈ kleinGroup := by
    fin_cases a
    · simp [leftKlein]
    all_goals
      apply conj_double_swap_mem g hg <;> decide
  have hr : g * rightKlein b * g⁻¹ ∈ kleinGroup := by
    fin_cases b
    · simp [rightKlein]
    all_goals
      apply conj_double_swap_mem g hg <;> decide
  simpa only [kleinPerm, mul_assoc, inv_mul_cancel_left] using kleinGroup.mul_mem hl hr

private theorem klein_commute : ∀ a b i : Fin 4,
    leftKlein i * kleinPerm a b = kleinPerm a b * leftKlein i ∧
    rightKlein i * kleinPerm a b = kleinPerm a b * rightKlein i := by decide

private theorem base_images : ∀ a b : Fin 8,
    rightKlein 1 a = a → leftKlein 1 b = b →
    ∃ c d : Fin 4, kleinPerm c d 0 = a ∧ kleinPerm c d 4 = b := by decide

private theorem klein_orbits : ∀ x : Fin 8,
    (∃ i : Fin 4, leftKlein i 0 = x) ∨ (∃ i : Fin 4, rightKlein i 4 = x) := by decide

private theorem klein_centralizer_le : centralizer (kleinGroup : Set S8) ≤ kleinGroup := by
  intro g hg
  have hl (i : Fin 4) (x : Fin 8) : leftKlein i (g x) = g (leftKlein i x) := by
    have hm : leftKlein i ∈ kleinGroup := ⟨i, 0, by simp [kleinPerm, rightKlein]⟩
    exact congrArg (fun q : S8 => q x) (hg _ hm)
  have hr (i : Fin 4) (x : Fin 8) : rightKlein i (g x) = g (rightKlein i x) := by
    have hm : rightKlein i ∈ kleinGroup := ⟨0, i, by simp [kleinPerm, leftKlein]⟩
    exact congrArg (fun q : S8 => q x) (hg _ hm)
  have h0 : rightKlein 1 (g 0) = g 0 := by
    simpa only [show rightKlein 1 0 = 0 from by decide] using hr 1 0
  have h4 : leftKlein 1 (g 4) = g 4 := by
    simpa only [show leftKlein 1 4 = 4 from by decide] using hl 1 4
  obtain ⟨a, b, ha, hb⟩ := base_images (g 0) (g 4) h0 h4
  refine ⟨a, b, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := klein_orbits x
  · calc
      g (leftKlein i 0) = leftKlein i (g 0) := (hl i 0).symm
      _ = leftKlein i (kleinPerm a b 0) := congrArg (leftKlein i) ha.symm
      _ = kleinPerm a b (leftKlein i 0) :=
        congrArg (fun q : S8 => q 0) (klein_commute a b i).1
  · calc
      g (rightKlein i 4) = rightKlein i (g 4) := (hr i 4).symm
      _ = rightKlein i (kleinPerm a b 4) := congrArg (rightKlein i) hb.symm
      _ = kleinPerm a b (rightKlein i 4) :=
        congrArg (fun q : S8 => q 4) (klein_commute a b i).2

private def liftedKlein : Subgroup X := (⊤ : Subgroup C2).prod kleinGroup

private theorem liftedKlein_pgroup : IsPGroup 2 liftedKlein := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  apply Prod.ext
  · have ht : ∀ z : C2, z ^ (2 ^ 1) = 1 := by decide
    exact ht g.val.1
  · obtain ⟨a, b, he⟩ := g.property.2
    change g.val.2 ^ (2 ^ 1) = 1
    simpa only [he, pow_one, pow_two] using klein_square a b

private theorem liftedKlein_le_core : liftedKlein ≤ fourOvergroup.pCoreIn 2 := by
  apply Subgroup.le_pCoreIn_of_normalizes liftedKlein_pgroup
  · exact Subgroup.prod_mono le_rfl klein_le_four
  · apply Subgroup.le_normalizer_iff.mpr
    intro g hg n hn
    refine ⟨mem_top _, ?_⟩
    exact (four_normalizes_klein hg.2 n.2).mp hn.2

/-- The two-block overgroup has characteristic two, using its intrinsic two-core. -/
theorem fourOvergroup_core_centralizer_le :
    fourOvergroup ⊓ centralizer (fourOvergroup.pCoreIn 2 : Set X) ≤ fourOvergroup.pCoreIn 2 := by
  rintro g ⟨_, hg⟩
  apply liftedKlein_le_core
  refine ⟨mem_top _, klein_centralizer_le ?_⟩
  intro n hn
  have hm : ((1 : C2), n) ∈ fourOvergroup.pCoreIn 2 :=
    liftedKlein_le_core ⟨mem_top _, hn⟩
  exact congrArg Prod.snd (hg _ hm)

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
