module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Basic
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Four half-root lines for the binary middle-node Levi

The roots (1/2,1/2,±1/2,±1/2), ordered (++,+−,−+,−−), span a four-dimensional
space in the actual F₄ Cartan-plus-root lattice. The positive middle simple
roots act on it by I+E₁₂ and I+E₀₁+E₂₃; the negative roots act by their
transposes.

Coordinate bounds exclude higher root-string terms. The integral simple-root
formulas then compute all 52 entries in each of the four columns, proving the
intertwining equations with the ambient matrices, including the absence of
components outside this space. Faithfulness on the whole Levi is a separate
obligation; injectivity of the four-line inclusion does not establish it.

Source: the middle-node Levi underlying Aschbacher–Smith F.1.12(I)(5), printed
pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`, using the integral Geck
root curves of `F4IntegralChevalleyRepresentation`.
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix

set_option linter.unusedSimpArgs false

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification

/-- Signs of the ordered half-roots (++,+−,−+,−−) in the last two coordinates. -/
def fourSigns (j : Fin 4) : Fin 4 → Bool :=
  ![![true, true, true, true], ![true, true, true, false],
    ![true, true, false, true], ![true, true, false, false]] j

/-- The four roots (1/2,1/2,±1/2,±1/2). -/
def fourRoot (j : Fin 4) : F4Chevalley.Root :=
  ⟨halfSignVector (fourSigns j), halfSignVector_mem_typeF4Roots _⟩

theorem fourRoot_injective : Function.Injective fourRoot := by
  intro i j h
  have h2 := congrArg (fun r : F4Chevalley.Root => r.val 2) h
  have h3 := congrArg (fun r : F4Chevalley.Root => r.val 3) h
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | (norm_num [fourRoot, fourSigns, halfSignVector, Matrix.cons_val_two,
      Matrix.cons_val_three] at h2 <;>
      norm_num [fourRoot, fourSigns, halfSignVector, Matrix.cons_val_two,
        Matrix.cons_val_three] at h3)

/-- The corresponding root coordinates of the Cartan-plus-root basis. -/
def fourIndex (j : Fin 4) : F4Chevalley.BasisIndex := Sum.inr (fourRoot j)

theorem fourIndex_injective : Function.Injective fourIndex :=
  Sum.inr_injective.comp fourRoot_injective

private theorem root_coordinate_bound (r : F4Chevalley.Root) (k : Fin 4) :
    -1 ≤ r.val k ∧ r.val k ≤ 1 := by
  rcases r with ⟨r, (h | h) | ⟨s, rfl⟩⟩
  · rcases h with ⟨i, j, hij, s, t, hs, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    all_goals
      by_cases hki : k = i
      · subst k
        simp [basisVector, Pi.single_apply, hij, Ne.symm hij]
      · by_cases hkj : k = j <;> simp [basisVector, Pi.single_apply, hki, hkj, hij, Ne.symm hij]
  · rcases h with ⟨i, rfl | rfl⟩ <;>
      by_cases hki : k = i <;> simp [basisVector, Pi.single_apply, hki]
  · simp only [halfSignVector]
    split_ifs <;> norm_num


private abbrev middleSimple (i : Fin 2) : typeF4RootPairing_base.support :=
  typeF4RootPairing_baseEquiv (if i = 0 then 1 else 2)

private theorem higher_add_absent (i : Fin 2) (j : Fin 4) (n : ℕ) (hn : 2 ≤ n) :
    typeF4RootPairing.root (fourRoot j) + n • typeF4RootPairing.root (middleSimple i) ∉
      Set.range typeF4RootPairing.root := by
  rintro ⟨r, hr⟩
  have h := root_coordinate_bound r (if i = 0 then 2 else 3)
  change r.val = _ at hr
  rw [hr] at h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  fin_cases i <;> fin_cases j <;>
    norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three] at h <;> linarith

private theorem higher_sub_absent (i : Fin 2) (j : Fin 4) (n : ℕ) (hn : 2 ≤ n) :
    typeF4RootPairing.root (fourRoot j) - n • typeF4RootPairing.root (middleSimple i) ∉
      Set.range typeF4RootPairing.root := by
  rintro ⟨r, hr⟩
  have h := root_coordinate_bound r (if i = 0 then 2 else 3)
  change r.val = _ at hr
  rw [hr] at h
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  fin_cases i <;> fin_cases j <;>
    norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three] at h <;> linarith

private theorem fourRoot_ne_signed_simple (i : Fin 2) (j : Fin 4) :
    fourRoot j ≠ (middleSimple i : F4Chevalley.Root) ∧
      fourRoot j ≠ typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple i) := by
  constructor <;> intro h
  all_goals
    have h0 := congrArg (fun r : F4Chevalley.Root => typeF4RootPairing.root r 0) h
    try simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] at h0
    fin_cases i <;> fin_cases j <;>
      norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot] at h0

private def positiveTarget (i : Fin 2) (j : Fin 4) : Option (Fin 4) :=
  if i = 0 then ![none, none, some 1, none] j else ![none, some 0, none, some 2] j

private def negativeTarget (i : Fin 2) (j : Fin 4) : Option (Fin 4) :=
  if i = 0 then ![none, some 2, none, none] j else ![some 1, none, some 3, none] j

private theorem positiveTarget_spec (i : Fin 2) (j : Fin 4) :
    match positiveTarget i j with
    | some k => typeF4RootPairing.root (fourRoot k) =
        typeF4RootPairing.root (middleSimple i) + typeF4RootPairing.root (fourRoot j) ∧
        typeF4RootPairing.chainBotCoeff (middleSimple i) (fourRoot j) = 0
    | none => typeF4RootPairing.root (middleSimple i) +
        typeF4RootPairing.root (fourRoot j) ∉ Set.range typeF4RootPairing.root := by
  fin_cases i <;> fin_cases j
  all_goals simp only [positiveTarget, Fin.zero_eta, Fin.isValue, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals try (constructor; · ext k; fin_cases k <;>
      norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
        Matrix.cons_val_two, Matrix.cons_val_three])
  all_goals try (apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr; right)
  all_goals
    rintro ⟨r, hr⟩
    have h2 := root_coordinate_bound r 2
    have h3 := root_coordinate_bound r 3
    change r.val = _ at hr
    rw [hr] at h2 h3
    norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three] at h2 <;>
      norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
        Matrix.cons_val_two, Matrix.cons_val_three] at h3

private theorem negativeTarget_spec (i : Fin 2) (j : Fin 4) :
    match negativeTarget i j with
    | some k => typeF4RootPairing.root (fourRoot k) =
        typeF4RootPairing.root (fourRoot j) - typeF4RootPairing.root (middleSimple i) ∧
        typeF4RootPairing.chainTopCoeff (middleSimple i) (fourRoot j) = 0
    | none => typeF4RootPairing.root (fourRoot j) -
        typeF4RootPairing.root (middleSimple i) ∉ Set.range typeF4RootPairing.root := by
  fin_cases i <;> fin_cases j
  all_goals simp only [negativeTarget, Fin.zero_eta, Fin.isValue, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals try (constructor; · ext k; fin_cases k <;>
      norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
        Matrix.cons_val_two, Matrix.cons_val_three])
  all_goals try (apply typeF4RootPairing.chainTopCoeff_eq_zero_iff.mpr; right)
  all_goals
    rintro ⟨r, hr⟩
    have h2 := root_coordinate_bound r 2
    have h3 := root_coordinate_bound r 3
    change r.val = _ at hr
    rw [hr] at h2 h3
    norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
      Matrix.cons_val_two, Matrix.cons_val_three] at h2 <;>
      norm_num [middleSimple, fourRoot, fourSigns, halfSignVector, typeF4SimpleRoot,
        Matrix.cons_val_two, Matrix.cons_val_three] at h3


private def targetColumn {R : Type*} [Zero R] [One R]
    (t : Option (Fin 4)) (r : F4Chevalley.BasisIndex) : R :=
  open scoped Classical in
  match t with
  | none => 0
  | some k => (Pi.single (fourIndex k) (1 : R) : F4Chevalley.BasisIndex → R) r

private theorem e_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) :
    eMatrix (middleSimple i) r (fourIndex j) =
      targetColumn (R := ℤ) (positiveTarget i j) r := by
  classical
  have ht := positiveTarget_spec i j
  cases h : positiveTarget i j with
  | none =>
    rw [h] at ht
    have hn := (fourRoot_ne_signed_simple i j).2
    have he := eMatrix_mulVec_v_zero (i := middleSimple i) (j := fourRoot j) hn ht
    simpa [targetColumn, h, v, fourIndex, Matrix.mulVec_single_one] using congrFun he r
  | some k =>
    rw [h] at ht
    have he := eMatrix_mulVec_v_add ht.1
    rw [ht.2] at he
    simpa [targetColumn, h, v, fourIndex, Matrix.mulVec_single_one] using congrFun he r

private theorem f_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) :
    fMatrix (middleSimple i) r (fourIndex j) =
      targetColumn (R := ℤ) (negativeTarget i j) r := by
  classical
  have ht := negativeTarget_spec i j
  cases h : negativeTarget i j with
  | none =>
    rw [h] at ht
    have hf := fMatrix_mulVec_v_zero (i := middleSimple i) (j := fourRoot j)
      (fourRoot_ne_signed_simple i j).1 ht
    simpa [targetColumn, h, v, fourIndex, Matrix.mulVec_single_one] using congrFun hf r
  | some k =>
    rw [h] at ht
    have hf := fMatrix_mulVec_v_sub ht.1
    rw [ht.2] at hf
    simpa [targetColumn, h, v, fourIndex, Matrix.mulVec_single_one] using congrFun hf r

private theorem e_higher_column (i : Fin 2) (j : Fin 4) (n : ℕ)
    (r : F4Chevalley.BasisIndex) :
    eDividedPower (middleSimple i) (n + 2) r (fourIndex j) = 0 := by
  have he := eDividedPower_add_two_mulVec_v_zero (middleSimple i) (fourRoot j) n
    (higher_add_absent i j (n + 2) (by omega))
  simpa [v, fourIndex, Matrix.mulVec_single_one] using congrFun he r

private theorem f_higher_column (i : Fin 2) (j : Fin 4) (n : ℕ)
    (r : F4Chevalley.BasisIndex) :
    fDividedPower (middleSimple i) (n + 2) r (fourIndex j) = 0 := by
  have hf := fDividedPower_add_two_mulVec_v_zero (middleSimple i) (fourRoot j) n
    (higher_sub_absent i j (n + 2) (by omega))
  simpa [v, fourIndex, Matrix.mulVec_single_one] using congrFun hf r

private theorem cast_targetColumn (t : Option (Fin 4)) (r : F4Chevalley.BasisIndex) :
    (targetColumn (R := ℤ) t r : CoefficientField 0) = targetColumn t r := by
  classical
  cases t <;> simp [targetColumn, Pi.single_apply, apply_ite]

private theorem positive_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) :
    positiveMatrix (middleSimple i) (1 : CoefficientField 0) r (fourIndex j) =
      (Pi.single (fourIndex j) (1 : CoefficientField 0) : F4Chevalley.BasisIndex → CoefficientField 0) r + targetColumn (positiveTarget i j) r := by
  classical
  simp only [positiveMatrix_formula, one_smul, one_pow, Matrix.add_apply,
    Matrix.map_apply, eDividedPower_one, e_column,
    e_higher_column i j 0, e_higher_column i j 1, map_zero, add_zero,
    Int.coe_castRingHom, cast_targetColumn]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

private theorem negative_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) :
    negativeMatrix (middleSimple i) (1 : CoefficientField 0) r (fourIndex j) =
      (Pi.single (fourIndex j) (1 : CoefficientField 0) : F4Chevalley.BasisIndex → CoefficientField 0) r + targetColumn (negativeTarget i j) r := by
  classical
  simp only [negativeMatrix_formula, one_smul, one_pow, Matrix.add_apply,
    Matrix.map_apply, fDividedPower_one, f_column,
    f_higher_column i j 0, f_higher_column i j 1, map_zero, add_zero,
    Int.coe_castRingHom, cast_targetColumn]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]


/-- The inclusion of the ordered four half-root lines into the F₄ lattice. -/
def fourEmbedding : Matrix F4Chevalley.BasisIndex (Fin 4) (CoefficientField 0) :=
  open scoped Classical in
  fun r j => if r = fourIndex j then 1 else 0

theorem fourEmbedding_mul (M : Matrix (Fin 4) (Fin 4) (CoefficientField 0))
    (i j : Fin 4) : (fourEmbedding * M) (fourIndex i) j = M i j := by
  classical
  simp [fourEmbedding, Matrix.mul_apply, fourIndex_injective.eq_iff]

theorem mul_fourEmbedding (A : MatrixCarrier 0)
    (r : F4Chevalley.BasisIndex) (j : Fin 4) :
    (A * fourEmbedding) r j = A r (fourIndex j) := by
  classical
  simp [fourEmbedding, Matrix.mul_apply]

theorem fourEmbedding_mul_injective :
    Function.Injective (fun M : Matrix (Fin 4) (Fin 4) (CoefficientField 0) =>
      fourEmbedding * M) := by
  intro M N h
  ext i j
  simpa only [fourEmbedding_mul] using congrArg (fun A => A (fourIndex i) j) h

/-- The given split Levi retains its actual 52-dimensional matrix action. -/
def ambientLeviHom : splitLevi →* MatrixUnits 0 :=
  (SplitGroup 0).subtype.comp splitLevi.subtype

private theorem signedRoot_curve (i : Fin 4) :
    F4Chevalley.rootCurve (signedRoot i) (1 : CoefficientField 0) =
      ![positiveUnit (middleSimple 0) 1, positiveUnit (middleSimple 1) 1,
        negativeUnit (middleSimple 0) 1, negativeUnit (middleSimple 1) 1] i := by
  fin_cases i
  · exact rootCurveUnit_simple (middleSimple 0) 1
  · exact rootCurveUnit_simple (middleSimple 1) 1
  · exact rootCurveUnit_neg_simple (middleSimple 0) 1
  · exact rootCurveUnit_neg_simple (middleSimple 1) 1

/-- The four root elements restrict to the required long and short matrices. -/
theorem splitGenerator_intertwines (i : Fin 4) :
    (ambientLeviHom (splitGenerator i)).val * fourEmbedding =
      fourEmbedding * (matrixGenerator i).val := by
  classical
  ext r j
  rw [mul_fourEmbedding]
  change (F4Chevalley.rootCurve (signedRoot i) (1 : CoefficientField 0)).val r
    (fourIndex j) = (fourEmbedding * generatorMatrix i) r j
  rw [signedRoot_curve]
  fin_cases i
  · change positiveMatrix (middleSimple 0) 1 r (fourIndex j) = _
    rw [positive_column]
    fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, generatorMatrix, fourEmbedding,
        targetColumn, positiveTarget, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm]
    exact add_comm _ _
  · change positiveMatrix (middleSimple 1) 1 r (fourIndex j) = _
    rw [positive_column]
    fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, generatorMatrix, fourEmbedding,
        targetColumn, positiveTarget, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm] <;>
      exact add_comm _ _
  · change negativeMatrix (middleSimple 0) 1 r (fourIndex j) = _
    rw [negative_column]
    fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, generatorMatrix, fourEmbedding,
        targetColumn, positiveTarget, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm]
  · change negativeMatrix (middleSimple 1) 1 r (fourIndex j) = _
    rw [negative_column]
    fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, generatorMatrix, fourEmbedding,
        targetColumn, positiveTarget, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm]

/-- The ambient map forgets subgroup proofs only. -/
theorem ambientLeviHom_injective : Function.Injective ambientLeviHom := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact h

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification
