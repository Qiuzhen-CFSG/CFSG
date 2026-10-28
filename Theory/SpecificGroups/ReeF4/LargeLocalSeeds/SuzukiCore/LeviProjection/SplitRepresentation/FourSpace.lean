module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.MatrixGraph
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# The general-field action on four half-root lines

The half-roots (1/2,1/2,±1/2,±1/2), in (++,+−,−+,−−) order, span an
invariant four-space for the middle simple root curves. The integral column
formulas give their literal matrices at arbitrary field parameters. Bounds
on root coordinates exclude every higher divided-power term and every row
outside the four-space.

The calculations are adapted from this repository's
`SuzukiRigidity/OppositeScales/FourLines.lean`, retaining their arbitrary
parameters and exposing the embedding for the split representation and its
kernel calculation. No faithfulness claim follows merely from this embedding.
Source: GLS3 §§2.3–2.4 and the Levi in Aschbacher–Smith F.1.12(I)(5), p.263.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
set_option linter.unusedSimpArgs false

namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
variable {m : ℕ}

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
    (targetColumn (R := ℤ) t r : CoefficientField m) = targetColumn t r := by
  classical
  cases t <;> simp [targetColumn, Pi.single_apply, apply_ite]

private theorem positive_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) (t : CoefficientField m) :
    positiveMatrix (middleSimple i) t r (fourIndex j) =
      (Pi.single (fourIndex j) (1 : CoefficientField m) : F4Chevalley.BasisIndex → CoefficientField m) r + t * targetColumn (positiveTarget i j) r := by
  classical
  simp only [positiveMatrix_formula, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.map_apply, eDividedPower_one, e_column,
    e_higher_column i j 0, e_higher_column i j 1, map_zero, mul_zero, add_zero,
    Int.coe_castRingHom, cast_targetColumn]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

private theorem negative_column (i : Fin 2) (j : Fin 4) (r : F4Chevalley.BasisIndex) (t : CoefficientField m) :
    negativeMatrix (middleSimple i) t r (fourIndex j) =
      (Pi.single (fourIndex j) (1 : CoefficientField m) : F4Chevalley.BasisIndex → CoefficientField m) r + t * targetColumn (negativeTarget i j) r := by
  classical
  simp only [negativeMatrix_formula, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.map_apply, fDividedPower_one, f_column,
    f_higher_column i j 0, f_higher_column i j 1, map_zero, mul_zero, add_zero,
    Int.coe_castRingHom, cast_targetColumn]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]


/-- The inclusion of the ordered four half-root lines into the F₄ lattice. -/
def fourEmbedding (m : ℕ) : Matrix F4Chevalley.BasisIndex (Fin 4) (CoefficientField m) :=
  open scoped Classical in
  fun r j => if r = fourIndex j then 1 else 0

theorem fourEmbedding_mul (M : Matrix (Fin 4) (Fin 4) (CoefficientField m))
    (i j : Fin 4) : (fourEmbedding m * M) (fourIndex i) j = M i j := by
  classical
  simp [fourEmbedding, Matrix.mul_apply, fourIndex_injective.eq_iff]

theorem mul_fourEmbedding (A : MatrixCarrier m)
    (r : F4Chevalley.BasisIndex) (j : Fin 4) :
    (A * fourEmbedding m) r j = A r (fourIndex j) := by
  classical
  simp [fourEmbedding, Matrix.mul_apply]

theorem fourEmbedding_mul_injective :
    Function.Injective (fun M : Matrix (Fin 4) (Fin 4) (CoefficientField m) =>
      fourEmbedding m * M) := by
  intro M N h
  ext i j
  simpa only [fourEmbedding_mul] using congrArg (fun A => A (fourIndex i) j) h


private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def simpleMatrix (positive : Bool) (i : Fin 2) (t : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  if positive then
    if i = 0 then !![1,0,0,0; 0,1,t,0; 0,0,1,0; 0,0,0,1]
    else !![1,t,0,0; 0,1,0,0; 0,0,1,t; 0,0,0,1]
  else
    if i = 0 then !![1,0,0,0; 0,1,0,0; 0,t,1,0; 0,0,0,1]
    else !![1,0,0,0; t,1,0,0; 0,0,1,0; 0,0,t,1]

private theorem simple_intertwines (positive : Bool) (i : Fin 2) (t : CoefficientField m) :
    (F4Chevalley.rootCurve (if positive then (middleSimple i : F4Chevalley.Root) else -(middleSimple i : F4Chevalley.Root)) t).val * fourEmbedding m =
      fourEmbedding m * simpleMatrix positive i t := by
  classical
  ext r j
  rw [mul_fourEmbedding]
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte,
      F4Chevalley.rootCurve, F4Chevalley.integralOperators, rootCurveUnit_neg_simple]
    change negativeMatrix (middleSimple i) t r (fourIndex j) = _
    rw [negative_column]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, simpleMatrix, fourEmbedding,
        targetColumn, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm]
  · simp only [↓reduceIte,
      F4Chevalley.rootCurve, F4Chevalley.integralOperators, rootCurveUnit_simple]
    change positiveMatrix (middleSimple i) t r (fourIndex j) = _
    rw [positive_column]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, simpleMatrix, fourEmbedding,
        targetColumn, positiveTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm] <;> ring

/-- The four literal signed simple-root images, in `MatrixGraph.signedRoot` order. -/
theorem signedRoot_intertwines (i : Fin 4) (t : CoefficientField m) :
    (F4Chevalley.rootCurve (signedRoot i) t).val * fourEmbedding m =
      fourEmbedding m * (matrixGenerator m i t).val := by
  fin_cases i
  · exact simple_intertwines true 0 t
  · exact simple_intertwines true 1 t
  · exact simple_intertwines false 0 t
  · exact simple_intertwines false 1 t

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
