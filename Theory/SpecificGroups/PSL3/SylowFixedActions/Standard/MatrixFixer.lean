module

public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.Model
public import Theory.SpecificGroups.PSL3.SylowFixedActions.Standard.ScalarLift

/-!
# The standard fixer of the order-four diagonal tests

Cubic scalar discrepancies disappear on elements of exponent four. For a
linear conjugation, the first diagonal test has three distinct eigenvalues,
so the conjugating matrix is diagonal. Fixing the coordinate interchange then
equates its first two entries, leaving only the action of `diag(1,1,t)`.
For a linear-times-graph action, the two diagonal equations instead force the
entire third row to vanish, contradicting invertibility.

Source: GLS3, §2.7, `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115; this
supplies the Sylow-fixed calculation for the linear alternatives in
Aschbacher–Smith F.6.18(10)–(11), pp.309–310, and 15.4.18, pp.1162–1163.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem unit_four_distinct (u : Fˣ) (hu : orderOf u = 4) :
    (u : F) ≠ 1 ∧ ((u⁻¹ : Fˣ) : F) ≠ 1 ∧ (u : F) ≠ ((u⁻¹ : Fˣ) : F) := by
  have h1 : u ≠ 1 := by intro h; simp [h] at hu
  have hi : u⁻¹ ≠ 1 := by simpa using h1
  refine ⟨fun h => h1 (Units.ext h), fun h => hi (Units.ext h), ?_⟩
  intro h
  have he : u = u⁻¹ := Units.ext h
  have h2 : u ^ 2 = 1 := by
    calc
      u ^ 2 = u * u⁻¹ := by rw [pow_two]; exact congrArg (u * ·) he
      _ = 1 := mul_inv_cancel u
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [hu] at hd
  norm_num at hd

private theorem linear_commutes_of_fix (g : GL (Fin 3) F) (x : SL(3, F))
    (hx : x ^ 4 = 1) (hfix : linearConj F g (projection F x) = projection F x) :
    g.val * x.val = x.val * g.val := by
  have hs : linearConjSL F g x = x :=
    (centerAction_fixes_iff_of_pow_four F (linearConjSL F g) x hx).mp hfix
  have he := congrArg SpecialLinearGroup.toGL hs
  rw [linearConjSL_toGL] at he
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)

omit [Finite F] in
private theorem intertwining_entry_zero (g : Matrix (Fin 3) (Fin 3) F)
    (d e : Fin 3 → F) (h : g * Matrix.diagonal d = Matrix.diagonal e * g)
    (i j : Fin 3) (hne : d j ≠ e i) : g i j = 0 := by
  have he := congrArg (fun m => m i j) h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  by_contra hn
  exact hne (mul_left_cancel₀ hn (he.trans (mul_comm _ _)))

private theorem linear_fixer_diagonal (u : Fˣ) (hu : orderOf u = 4)
    (g : GL (Fin 3) F)
    (hfix : linearConj F g (projection F (testDiagonal₁ F u)) =
      projection F (testDiagonal₁ F u)) :
    ∀ i j, i ≠ j → g.val i j = 0 := by
  have hpow : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have h := linear_commutes_of_fix g (testDiagonal₁ F u) (testDiagonal₁_pow_four F u hpow) hfix
  have hval : (testDiagonal₁ F u).val = Matrix.diagonal ![(u : F), ((u⁻¹ : Fˣ) : F), 1] := by
    simp [testDiagonal₁]
  rw [hval] at h
  obtain ⟨h1, hi1, hni⟩ := unit_four_distinct u hu
  intro i j hij
  apply intertwining_entry_zero g.val _ _ h i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hij rfl)
    | exact h1
    | exact Ne.symm h1
    | exact hi1
    | exact Ne.symm hi1
    | exact hni
    | exact Ne.symm hni

private theorem linear_fixer_first_two_eq (g : GL (Fin 3) F)
    (hfix : linearConj F g (projection F (interchange F)) = projection F (interchange F)) :
    g.val 0 0 = g.val 1 1 := by
  have hx : interchange F ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, interchange_sq, one_pow]
  have h := linear_commutes_of_fix g (interchange F) hx hfix
  have he := congrArg (fun m => m 0 1) h
  simpa [interchange, Matrix.mul_apply, Fin.sum_univ_three] using he

omit [Finite F] in
private theorem linearConj_scalar (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := projection_surjective F y
  change projection F (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) = projection F x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

/-- A linear automorphism fixing the three tests is in the one-parameter torus. -/
theorem linear_fixes_tests_mem_range (u : Fˣ) (hu : orderOf u = 4)
    (g : GL (Fin 3) F)
    (hfix : ∀ x ∈ testSet F u, linearConj F g x = x) :
    linearConj F g ∈ (fixerAction F).range := by
  have hd := linear_fixer_diagonal u hu g (hfix _ (by simp [testSet]))
  have hab := linear_fixer_first_two_eq g (hfix _ (by simp [testSet]))
  have hdet : g.val 0 0 * g.val 1 1 * g.val 2 2 ≠ 0 := by
    have h := (GeneralLinearGroup.det g).ne_zero
    change Matrix.det g.val ≠ 0 at h
    simpa [Matrix.det_fin_three, hd 0 1 (by decide), hd 0 2 (by decide),
      hd 1 0 (by decide), hd 1 2 (by decide), hd 2 0 (by decide), hd 2 1 (by decide)] using h
  have ha : g.val 0 0 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hdet).1).1
  have hc : g.val 2 2 ≠ 0 := (mul_ne_zero_iff.mp hdet).2
  let a : Fˣ := Units.mk0 (g.val 0 0) ha
  let c : Fˣ := Units.mk0 (g.val 2 2) hc
  have he : g = GeneralLinearGroup.scalar (Fin 3) a * fixerMatrix F (c * a⁻¹) := by
    apply Units.ext
    ext i j
    change g.val i j = (Matrix.scalar (Fin 3) (g.val 0 0) *
      Matrix.diagonal ![1, 1, (g.val 2 2) * (g.val 0 0)⁻¹]) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, hd, ← hab, ha, mul_comm]
  refine ⟨c * a⁻¹, ?_⟩
  change linearConj F (fixerMatrix F (c * a⁻¹)) = linearConj F g
  rw [he, (linearConj F).map_mul, linearConj_scalar, one_mul]

omit [Finite F] in
private theorem graphSL_diagonal (a : Fˣ × Fˣ) :
    graphSL F (diagonalSL F a) = diagonalSL F a⁻¹ := by
  change (SpecialLinearGroup.transpose (diagonalSL F a))⁻¹ = _
  rw [map_inv]
  congr 1
  apply Subtype.ext
  exact Matrix.isSymm_diagonal _

private theorem graph_intertwines_diagonal (g : GL (Fin 3) F) (a : Fˣ × Fˣ)
    (hx : diagonalSL F a ^ 4 = 1)
    (hfix : (linearConj F g * graph F) (projection F (diagonalSL F a)) =
      projection F (diagonalSL F a)) :
    g.val * (diagonalSL F a⁻¹).val = (diagonalSL F a).val * g.val := by
  have hs := (centerAction_fixes_iff_of_pow_four F
    (linearConjSL F g * graphSL F) (diagonalSL F a) hx).mp hfix
  change linearConjSL F g (graphSL F (diagonalSL F a)) = diagonalSL F a at hs
  rw [graphSL_diagonal] at hs
  have he := congrArg SpecialLinearGroup.toGL hs
  rw [linearConjSL_toGL] at he
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp he)

/-- No linear-times-graph automorphism fixes the diagonal tests simultaneously. -/
theorem graph_not_fixes_tests (u : Fˣ) (hu : orderOf u = 4)
    (g : GL (Fin 3) F) :
    ¬ ∀ x ∈ testSet F u, (linearConj F g * graph F) x = x := by
  intro hfix
  have hpow : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have h₁ := graph_intertwines_diagonal g (u, u⁻¹) (testDiagonal₁_pow_four F u hpow)
    (hfix _ (by simp [testSet, testDiagonal₁]))
  have h₂ := graph_intertwines_diagonal g (1, u) (testDiagonal₂_pow_four F u hpow)
    (hfix _ (by simp [testSet, testDiagonal₂]))
  have hv₁ : (diagonalSL F (u, u⁻¹)).val =
      Matrix.diagonal ![(u : F), ((u⁻¹ : Fˣ) : F), 1] := by simp
  have hvi₁ : (diagonalSL F (u, u⁻¹)⁻¹).val =
      Matrix.diagonal ![((u⁻¹ : Fˣ) : F), (u : F), 1] := by simp
  have hv₂ : (diagonalSL F (1, u)).val =
      Matrix.diagonal ![1, (u : F), ((u⁻¹ : Fˣ) : F)] := by simp
  have hvi₂ : (diagonalSL F (1, u)⁻¹).val =
      Matrix.diagonal ![1, ((u⁻¹ : Fˣ) : F), (u : F)] := by simp
  rw [hv₁, hvi₁] at h₁
  rw [hv₂, hvi₂] at h₂
  obtain ⟨h1, hi1, hni⟩ := unit_four_distinct u hu
  have h20 : g.val 2 0 = 0 := intertwining_entry_zero g.val _ _ h₁ 2 0 hi1
  have h21 : g.val 2 1 = 0 := intertwining_entry_zero g.val _ _ h₁ 2 1 h1
  have h22 : g.val 2 2 = 0 := intertwining_entry_zero g.val _ _ h₂ 2 2 hni
  have hdet := (GeneralLinearGroup.det g).ne_zero
  change Matrix.det g.val ≠ 0 at hdet
  exact hdet (by simp [Matrix.det_fin_three, h20, h21, h22])

end Matrix.PSL3.SylowFixedActions.Standard
