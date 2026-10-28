module

public import Theory.Character.AlternatingSix.Blocks
public import Theory.Character.AlternatingSix.Golden.Interfaces
public import Theory.Character.AlternatingSix.Golden.Completion
public import Theory.Character.AlternatingSix.Golden.ClassGeometry

/-!
# The two golden character rows of A₆ from the rational block

Starting with two actual irreducibles complementary to the principal and four
rational characters, the identity column forces their degrees to be eight:
the two remaining squared degrees sum to 128. Saturated columns give the
zeros at orders two and four; equality in the order-three column bound gives
both values minus one. The real five-element columns then give the golden
quadratic equation, and their mutual orthogonality gives the interchange at
squaring.

The complete irreducible-character basis and the intrinsic seven-class
calculation supply both construction inputs. Thus `goldenBlock_of_rational`
requires only the supplied rational block and the orders of the two markings.
Both resulting rows are actual irreducible representation characters.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
§6, pp.10–11, the two degree-eight rows; ordinary column orthogonality.
-/

open scoped BigOperators
noncomputable section
namespace Theory.Character.AlternatingSix

private theorem character_conj {G : Type*} [Group G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) {x y : G} (h : IsConj x y) : χ x = χ y := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  exact congrArg (characterClassFunction ρ) (ConjClasses.mk_eq_mk_iff_isConj.mpr h)

variable {c : alternatingGroup (Fin 6)} (R : RationalBlock c)

private theorem rationalColumn_one : rationalColumn R 1 1 = 232 := by
  norm_num [rationalColumn, R.one, rationalValues, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem rationalColumn_two (x : alternatingGroup (Fin 6)) (hx : orderOf x = 2) :
    rationalColumn R x x = 8 := by
  norm_num [rationalColumn, fun j => R.two j x hx, rationalValues, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem rationalColumn_four (x : alternatingGroup (Fin 6)) (hx : orderOf x = 4) :
    rationalColumn R x x = 4 := by
  norm_num [rationalColumn, fun j => R.four j x hx, rationalValues, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem rationalColumn_three (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) :
    rationalColumn R x x = 7 ∧ rationalColumn R x 1 = 16 := by
  by_cases hxc : IsConj x c
  · have hv : ∀ j, R.character j x = (rationalValues j 2 : ℂ) :=
      fun j => (character_conj (R.irreducible j) hxc).trans (R.three j)
    norm_num [rationalColumn, hv, R.one, rationalValues, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · norm_num [rationalColumn, fun j => R.otherThree j x hx hxc, R.one,
      rationalValues, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem rationalColumn_five (x y : alternatingGroup (Fin 6))
    (hx : orderOf x = 5) (hy : orderOf y = 5) :
    rationalColumn R x y = 2 ∧ rationalColumn R x 1 = -8 := by
  have hv : ∀ j : Fin 4, rationalValues j 5 = ![-1, 0, 0, 0] j := by
    intro j
    fin_cases j <;> rfl
  simp only [rationalColumn, R.five _ x hx, R.five _ y hy, R.one, hv]
  norm_num [rationalValues, Fin.sum_univ_succ]

private theorem pair_zero {a b : ℂ}
    (h : a * star a + b * star b = 0) : a = 0 ∧ b = 0 := by
  have hr : Complex.normSq a + Complex.normSq b = 0 := by
    simpa [Complex.star_def, Complex.mul_conj] using congrArg Complex.re h
  constructor <;> apply Complex.normSq_eq_zero.mp
  · linarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]
  · linarith [Complex.normSq_nonneg a, Complex.normSq_nonneg b]

private theorem pair_neg_one {a b : ℂ}
    (h : a * star a + b * star b = 2) (hs : a + b = -2) :
    a = -1 ∧ b = -1 := by
  have hr : Complex.normSq a + Complex.normSq b = 2 := by
    simpa [Complex.star_def, Complex.mul_conj] using congrArg Complex.re h
  have hsre := congrArg Complex.re hs
  have hsi := congrArg Complex.im hs
  norm_num at hsre hsi
  have ha : Complex.normSq (a + 1) = 0 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, add_zero] at hr ⊢
    nlinarith [sq_nonneg (a.re + 1), sq_nonneg (b.re + 1),
      sq_nonneg a.im, sq_nonneg b.im]
  have ha' : a = -1 := eq_neg_of_add_eq_zero_left (Complex.normSq_eq_zero.mp ha)
  exact ⟨ha', by linear_combination hs - congrArg (fun z : ℂ => z) ha'⟩

private theorem squares_nat (n m : ℕ) (h : n ^ 2 + m ^ 2 = 128) : n = 8 ∧ m = 8 := by
  have hn : n ≤ 11 := by nlinarith [sq_nonneg (n : ℤ)]
  have hm : m ≤ 11 := by nlinarith [sq_nonneg (m : ℤ)]
  interval_cases n <;> interval_cases m <;> (try norm_num at *)

variable (C : RationalCompletion R)

private theorem degrees : ∀ j, C.character j 1 = 8 := by
  have hcard : Nat.card (Subgroup.centralizer ({(1 : alternatingGroup (Fin 6))} : Set _)) = 360 := by
    have ht : Subgroup.centralizer ({(1 : alternatingGroup (Fin 6))} : Set _) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [ht, Nat.card_congr (Subgroup.topEquiv.toEquiv), nat_card_alternatingGroup]
    norm_num
  have h := C.column 1 1
  rw [if_pos (IsConj.refl _), hcard, rationalColumn_one] at h
  obtain ⟨n, ρ, _, hρ⟩ := C.irreducible 0
  obtain ⟨m, σ, _, hσ⟩ := C.irreducible 1
  have hn : C.character 0 1 = (n : ℂ) := by simp [hρ, Representation.char_one]
  have hm : C.character 1 1 = (m : ℂ) := by simp [hσ, Representation.char_one]
  rw [hn, hm] at h
  norm_num only [star_natCast] at h
  have heq : n ^ 2 + m ^ 2 = 128 := by
    have hc : (n : ℂ) ^ 2 + (m : ℂ) ^ 2 = 128 := by linear_combination h
    exact_mod_cast hc
  obtain ⟨rfl, rfl⟩ := squares_nat n m heq
  intro j
  fin_cases j <;> assumption

private theorem sum_values (x : alternatingGroup (Fin 6)) (hx : x ≠ 1) :
    C.character 0 x + C.character 1 x = -rationalColumn R x 1 / 8 := by
  have h := C.column x 1
  rw [if_neg (by simpa only [isConj_one_left] using hx), degrees R C 0,
    degrees R C 1] at h
  norm_num at h
  linear_combination h / 8

private theorem value_two (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 2) :
    ∀ j, C.character j x = 0 := by
  have h := C.column x x
  rw [if_pos (IsConj.refl _), F.centralizer_two x hx, rationalColumn_two R x hx] at h
  norm_num at h
  obtain ⟨h0, h1⟩ := pair_zero h
  intro j
  fin_cases j <;> assumption

private theorem value_four (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 4) :
    ∀ j, C.character j x = 0 := by
  have h := C.column x x
  rw [if_pos (IsConj.refl _), F.centralizer_four x hx, rationalColumn_four R x hx] at h
  norm_num at h
  obtain ⟨h0, h1⟩ := pair_zero h
  intro j
  fin_cases j <;> assumption

private theorem value_three (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) :
    ∀ j, C.character j x = -1 := by
  have h := C.column x x
  rw [if_pos (IsConj.refl _), F.centralizer_three x hx, (rationalColumn_three R x hx).1] at h
  norm_num at h
  have hs := sum_values R C x (by intro he; subst x; simp at hx)
  rw [(rationalColumn_three R x hx).2] at hs
  norm_num at hs
  obtain ⟨h0, h1⟩ := pair_neg_one h hs
  intro j
  fin_cases j <;> assumption

private theorem five_star (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) (j : Fin 2) :
    star (C.character j x) = C.character j x := by
  have he := character_conj (C.irreducible j) (F.five_inverse x hx)
  obtain ⟨n, ρ, _, hρ⟩ := C.irreducible j
  rw [hρ, Representation.representation_character_inv_eq_star_character] at he
  simpa only [hρ] using he.symm

private theorem five_sum (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) :
    C.character 0 x + C.character 1 x = 1 := by
  have hs := sum_values R C x (by intro he; subst x; simp at hx)
  rw [(rationalColumn_five R x x hx hx).2] at hs
  norm_num at hs
  exact hs

private theorem five_quadratic (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) :
    C.character 0 x ^ 2 = C.character 0 x + 1 := by
  have h := C.column x x
  rw [if_pos (IsConj.refl _), F.centralizer_five x hx,
    (rationalColumn_five R x x hx hx).1, five_star R C F x hx 0,
    five_star R C F x hx 1] at h
  have hs := five_sum R C x hx
  have h1 : C.character 1 x = 1 - C.character 0 x := by linear_combination hs
  rw [h1] at h
  linear_combination h / 2

private theorem five_square_values (F : GoldenClassGeometry) (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) :
    C.character 0 (x ^ 2) = 1 - C.character 0 x ∧
      C.character 1 (x ^ 2) = C.character 0 x := by
  have hx2 : orderOf (x ^ 2) = 5 := by rw [orderOf_pow, hx]; decide
  have h := C.column x (x ^ 2)
  rw [if_neg (F.five_square x hx), (rationalColumn_five R x (x ^ 2) hx hx2).1,
    five_star R C F (x ^ 2) hx2 0, five_star R C F (x ^ 2) hx2 1] at h
  have hs := five_sum R C x hx
  have hs2 := five_sum R C (x ^ 2) hx2
  have hq := five_quadratic R C F x hx
  have h1 : C.character 1 x = 1 - C.character 0 x := by linear_combination hs
  have h2 : C.character 1 (x ^ 2) = 1 - C.character 0 (x ^ 2) := by linear_combination hs2
  rw [h1, h2] at h
  have hprod : (2 * C.character 0 x - 1) *
      (C.character 0 (x ^ 2) - (1 - C.character 0 x)) = 0 := by
    linear_combination h + 2 * hq
  have hne : 2 * C.character 0 x - 1 ≠ 0 := by
    intro he
    have hz : (5 : ℂ) = 0 := by
      linear_combination -4 * hq + (2 * C.character 0 x - 1) * he
    norm_num at hz
  have hv := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)
  exact ⟨hv, by linear_combination hs2 - hv⟩

/-- Recover both golden rows from the actual complementary irreducibles.
Their degrees, all low-order values, and the marked quadratic values are
consequences of column orthogonality and the intrinsic class geometry. -/
public def goldenBlockOfCompletion (F : GoldenClassGeometry)
    {μ : alternatingGroup (Fin 6)} (hμ : orderOf μ = 5) : GoldenBlock μ where
  parameter := C.character 0 μ
  parameter_equation := five_quadratic R C F μ hμ
  character := C.character
  irreducible := C.irreducible
  one := degrees R C
  two j x hx := value_two R C F x hx j
  three j x hx := value_three R C F x hx j
  four j x hx := value_four R C F x hx j
  five := by
    intro j
    fin_cases j
    · rfl
    · change C.character 1 μ = 1 - C.character 0 μ
      linear_combination five_sum R C μ hμ
  five_sq := by
    intro j
    have h := five_square_values R C F μ hμ
    fin_cases j
    · exact h.1
    · exact h.2

/-- Existence form of the complementary-character deduction.
This interface keeps the basis completion and class geometry explicit. -/
public theorem goldenBlock_of_completion (R : RationalBlock c) (C : RationalCompletion R) (F : GoldenClassGeometry)
    {μ : alternatingGroup (Fin 6)} (hμ : orderOf μ = 5) : Nonempty (GoldenBlock μ) :=
  ⟨goldenBlockOfCompletion R C F hμ⟩

/-- The four supplied rational characters determine two genuine degree-eight
irreducibles with every entry of `GoldenBlock`, for any order-five marking.
The complete irreducible basis and the intrinsic A₆ conjugacy calculation
discharge the two inputs of `goldenBlock_of_completion`. -/
public theorem goldenBlock_of_rational (c μ : alternatingGroup (Fin 6))
    (hc : orderOf c = 3) (hμ : orderOf μ = 5) (R : RationalBlock c) :
    Nonempty (GoldenBlock μ) := by
  obtain ⟨C⟩ := rationalCompletion_of_class_count c hc R goldenClassGeometry.class_count
  exact goldenBlock_of_completion R C goldenClassGeometry hμ

end Theory.Character.AlternatingSix
