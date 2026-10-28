module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.UnsignedAction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Detecting inverse parameters on opposite central Suzuki curves

The four half-root lines (1/2,1/2,±1/2,±1/2) are invariant under the middle
root groups. On these lines the two central type V curves have upper and lower
triangular four-by-four matrices. The (1,2) entry of their alternating
five-factor relation gives `v * theta(u)^2 * (u*v-1) = 0`. Thus nonzero
parameters satisfying this actual group relation are inverse.

The simple-root column arguments extend the binary calculation in
`ParabolicAmalgam/BinaryLocals/SuzukiProjection/MatrixIdentification/Representation/FourSpace.lean`
to arbitrary parameters in the Ree coefficient field. Integral Weyl transport
then supplies the two nonsimple roots. Every intertwining equation includes
all ambient rows; no faithfulness or identification of a rank-one quotient is
assumed. This proves a necessary condition on a relation, not its existence.

Source: GLS3, Table 2.4 type V and §§2.4–2.5, in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix
set_option linter.unusedSimpArgs false
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity.OppositeScales
variable {m : ℕ}
/-- Signs of the ordered half-roots (++,+−,−+,−−) in the last two coordinates. -/
private def fourSigns (j : Fin 4) : Fin 4 → Bool :=
  ![![true, true, true, true], ![true, true, true, false],
    ![true, true, false, true], ![true, true, false, false]] j

/-- The four roots (1/2,1/2,±1/2,±1/2). -/
private def fourRoot (j : Fin 4) : F4Chevalley.Root :=
  ⟨halfSignVector (fourSigns j), halfSignVector_mem_typeF4Roots _⟩

private theorem fourRoot_injective : Function.Injective fourRoot := by
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
private def fourIndex (j : Fin 4) : F4Chevalley.BasisIndex := Sum.inr (fourRoot j)

private theorem fourIndex_injective : Function.Injective fourIndex :=
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
private def fourEmbedding (m : ℕ) : Matrix F4Chevalley.BasisIndex (Fin 4) (CoefficientField m) :=
  open scoped Classical in
  fun r j => if r = fourIndex j then 1 else 0

private theorem fourEmbedding_mul (M : Matrix (Fin 4) (Fin 4) (CoefficientField m))
    (i j : Fin 4) : (fourEmbedding m * M) (fourIndex i) j = M i j := by
  classical
  simp [fourEmbedding, Matrix.mul_apply, fourIndex_injective.eq_iff]

private theorem mul_fourEmbedding (A : MatrixCarrier m)
    (r : F4Chevalley.BasisIndex) (j : Fin 4) :
    (A * fourEmbedding m) r j = A r (fourIndex j) := by
  classical
  simp [fourEmbedding, Matrix.mul_apply]

private theorem fourEmbedding_mul_injective :
    Function.Injective (fun M : Matrix (Fin 4) (Fin 4) (CoefficientField m) =>
      fourEmbedding m * M) := by
  intro M N h
  ext i j
  simpa only [fourEmbedding_mul] using congrArg (fun A => A (fourIndex i) j) h


local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def simpleMatrix (positive : Bool) (i : Fin 2) (t : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  if positive then
    if i = 0 then !![1,0,0,0; 0,1,t,0; 0,0,1,0; 0,0,0,1]
    else !![1,t,0,0; 0,1,0,0; 0,0,1,t; 0,0,0,1]
  else
    if i = 0 then !![1,0,0,0; 0,1,0,0; 0,t,1,0; 0,0,0,1]
    else !![1,0,0,0; t,1,0,0; 0,0,1,0; 0,0,t,1]

private theorem simple_intertwines (positive : Bool) (i : Fin 2) (t : CoefficientField m) :
    (F4Chevalley.rootCurve (signedRoot positive (middleSimple i)) t).val * fourEmbedding m =
      fourEmbedding m * simpleMatrix positive i t := by
  classical
  ext r j
  rw [mul_fourEmbedding]
  cases positive
  · simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
      F4Chevalley.rootCurve, F4Chevalley.integralOperators, rootCurveUnit_neg_simple]
    change negativeMatrix (middleSimple i) t r (fourIndex j) = _
    rw [negative_column]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, simpleMatrix, fourEmbedding,
        targetColumn, negativeTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm]
  · simp only [signedRoot, ↓reduceIte,
      F4Chevalley.rootCurve, F4Chevalley.integralOperators, rootCurveUnit_simple]
    change positiveMatrix (middleSimple i) t r (fourIndex j) = _
    rw [positive_column]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, simpleMatrix, fourEmbedding,
        targetColumn, positiveTarget, Pi.single_apply,
        Matrix.cons_val_two, Matrix.cons_val_three, eq_comm] <;> ring

private theorem intertwines_mul {x y : MatrixUnits m}
    {X Y : Matrix (Fin 4) (Fin 4) (CoefficientField m)}
    (hx : x.val * fourEmbedding m = fourEmbedding m * X)
    (hy : y.val * fourEmbedding m = fourEmbedding m * Y) :
    (x*y).val * fourEmbedding m = fourEmbedding m * (X*Y) := by
  change (x.val * y.val) * fourEmbedding m = _
  rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

private def weylMatrix (i : Fin 2) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  if i = 0 then !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  else !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

private theorem weyl_intertwines (i : Fin 2) :
    (WordRelations.titsUnit (S := CoefficientField m) [middleSimple i]).val * fourEmbedding m =
      fourEmbedding m * weylMatrix i := by
  have h := intertwines_mul (intertwines_mul (simple_intertwines true i (1 : CoefficientField m))
    (simple_intertwines false i 1)) (simple_intertwines true i 1)
  have he : simpleMatrix true i (1 : CoefficientField m) * simpleMatrix false i 1 *
      simpleMatrix true i 1 = weylMatrix i := by
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [simpleMatrix, weylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
        CharTwo.add_self_eq_zero]
  simpa only [WordRelations.titsUnit_cons, WordRelations.titsUnit_nil, mul_one,
    CharTwo.neg_eq, signedRoot, ↓reduceIte, Bool.false_eq_true, he] using h

private theorem weyl_inv (i : Fin 2) :
    (WordRelations.titsUnit (S := CoefficientField m) [middleSimple i])⁻¹ =
      WordRelations.titsUnit [middleSimple i] := by
  simp only [WordRelations.titsUnit_cons, WordRelations.titsUnit_nil, mul_one,
    mul_inv_rev, F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  group

private theorem reflected_intertwines (positive : Bool) (i j : Fin 2)
    (hr : typeF4RootPairing_base.IsPos
      (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j)))
    (t : CoefficientField m) :
    (F4Chevalley.rootCurve (signedRoot positive
      (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j))) t).val *
      fourEmbedding m = fourEmbedding m *
        (weylMatrix i * simpleMatrix positive j t * weylMatrix i) := by
  have h := intertwines_mul (intertwines_mul (weyl_intertwines i)
    (simple_intertwines positive j t)) (weyl_intertwines i)
  have hc : F4Chevalley.rootCurve (signedRoot positive
      (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j))) t =
      WordRelations.titsUnit [middleSimple i] *
        F4Chevalley.rootCurve (signedRoot positive (middleSimple j)) t *
          WordRelations.titsUnit [middleSimple i] := by
    cases positive
    · simpa only [weyl_inv, signedRoot, Bool.false_eq_true, ↓reduceIte] using WordRelations.rootCurve_neg_of_pos_transport _ hr
        [middleSimple i] (middleSimple j) rfl t
    · simpa only [weyl_inv, signedRoot, Bool.false_eq_true, ↓reduceIte] using WordRelations.rootCurve_of_pos_transport _ hr
        [middleSimple i] (middleSimple j) rfl t
  rw [hc]
  exact h

private theorem reflected_pos (i j : Fin 2) (hij : i ≠ j) :
    typeF4RootPairing_base.IsPos
      (typeF4RootPairing.reflectionPerm (middleSimple i) (middleSimple j)) := by
  apply (typeF4RootPairing_base.isPos_of_mem_support (middleSimple j).property).reflectionPerm
    (middleSimple i).property
  intro h
  have he := typeF4RootPairing_baseEquiv.injective (Subtype.ext h)
  fin_cases i <;> fin_cases j <;> first
  | exact hij rfl
  | contradiction

/-- The central type V curve on four invariant half-root lines. -/
private def centralMatrix (positive : Bool) (u : CoefficientField m) :
    Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  if positive then
    !![1, 0, theta m u, u; 0, 1, 0, theta m u; 0, 0, 1, 0; 0, 0, 0, 1]
  else
    !![1, 0, 0, 0; 0, 1, 0, 0; theta m u, 0, 1, 0; u, theta m u, 0, 1]

/-- This is an equality with the actual 52-dimensional root word, including
vanishing of every component outside the four chosen lines. -/
private theorem central_intertwines (positive : Bool) (u : CoefficientField m) :
    (suzukiWord m positive 0 u).val.val * fourEmbedding m =
      fourEmbedding m * centralMatrix positive u := by
  have hh := reflected_intertwines positive 1 0 (reflected_pos 1 0 (by decide)) u
  have hg := reflected_intertwines positive 0 1 (reflected_pos 0 1 (by decide)) (theta m u)
  have h := intertwines_mul hh hg
  have he : (weylMatrix 1 * simpleMatrix positive 0 u * weylMatrix 1) *
      (weylMatrix 0 * simpleMatrix positive 1 (theta m u) * weylMatrix 0) =
      centralMatrix positive u := by
    ext i j
    cases positive <;> fin_cases i <;> fin_cases j <;>
      simp [weylMatrix, simpleMatrix, centralMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  rw [he] at h
  simpa [suzukiWord_coe, suzukiRoots, middleSimple,
    Matrix.cons_val_two, Matrix.cons_val_three] using h

/-- The alternating word of length five. -/
def fivefold {M : Type*} [Mul M] (x y : M) : M := x * y * x * y * x

private theorem fivefold_intertwines {x y : MatrixUnits m}
    {X Y : Matrix (Fin 4) (Fin 4) (CoefficientField m)}
    (hx : x.val * fourEmbedding m = fourEmbedding m * X)
    (hy : y.val * fourEmbedding m = fourEmbedding m * Y) :
    (fivefold x y).val * fourEmbedding m = fourEmbedding m * fivefold X Y :=
  intertwines_mul (intertwines_mul (intertwines_mul (intertwines_mul hx hy) hx) hy) hx

private theorem centralMatrix_relation_parameter (u v : CoefficientField m)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : fivefold (centralMatrix true u) (centralMatrix false v) =
      fivefold (centralMatrix false v) (centralMatrix true u)) : u * v = 1 := by
  have ht : theta m u ≠ 0 := (map_ne_zero (theta m)).mpr hu
  have htwo : (2 : CoefficientField m) = 0 := CharTwo.two_eq_zero
  have hfour : (4 : CoefficientField m) = 0 := by
    calc
      (4 : CoefficientField m) = 2 + 2 := by norm_num
      _ = 0 := by simp only [htwo, add_zero]
  have he : (v * (theta m u)^2) * (u * v) = (v * (theta m u)^2) * 1 := by
    calc
      _ = (fivefold (centralMatrix true u) (centralMatrix false v)) 1 2 := by
        simp [fivefold, centralMatrix, Matrix.mul_apply, Fin.sum_univ_four]
        ring_nf
        simp only [htwo, hfour, mul_zero, zero_add, add_zero]
      _ = (fivefold (centralMatrix false v) (centralMatrix true u)) 1 2 :=
        congrArg (fun M => M 1 2) h
      _ = _ := by
        simp [fivefold, centralMatrix, Matrix.mul_apply, Fin.sum_univ_four]
        ring
  exact mul_left_cancel₀ (mul_ne_zero hv (pow_ne_zero _ ht)) he

/-- An alternating five-factor relation between nontrivial opposite central
Suzuki elements forces their parameters to be inverse. The test is made on
four invariant lines of the actual F₄ lattice, so no model identification or
faithfulness of a rank-one quotient is needed. -/
theorem central_fivefold_parameters (u v : CoefficientField m)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : fivefold (suzukiWord m true 0 u) (suzukiWord m false 0 v) =
      fivefold (suzukiWord m false 0 v) (suzukiWord m true 0 u)) : u * v = 1 := by
  apply centralMatrix_relation_parameter u v hu hv
  apply fourEmbedding_mul_injective
  calc
    fourEmbedding m * fivefold (centralMatrix true u) (centralMatrix false v) =
        (fivefold (suzukiWord m true 0 u) (suzukiWord m false 0 v)).val.val *
          fourEmbedding m :=
      (fivefold_intertwines (central_intertwines true u) (central_intertwines false v)).symm
    _ = (fivefold (suzukiWord m false 0 v) (suzukiWord m true 0 u)).val.val *
          fourEmbedding m := congrArg (fun x : SplitGroup m => x.val.val * fourEmbedding m) h
    _ = fourEmbedding m * fivefold (centralMatrix false v) (centralMatrix true u) :=
      fivefold_intertwines (central_intertwines false v) (central_intertwines true u)

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity.OppositeScales
end
