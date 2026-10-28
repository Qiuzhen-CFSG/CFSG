module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.SuzukiWitness.WordCalculation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.Columns
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation


/-!
# A middle-root square outside the Suzuki radical

The coroot combination `(4, 7, 5, 3)` measures the sum of the outer simple
coefficients. Every Suzuki radical root has positive degree, so its root
matrix is identity plus a strictly degree-raising matrix. Products and
inverses preserve this property. The middle root γ has degree zero;
consequently every radical matrix has zero in its γ row and Cartan columns.

For `x_γ(1) x_δ(1)`, the Cartan column at node zero instead has entry one.
Both roots have degree one for the negative node-zero coroot. Divided-power
homogeneity kills all higher terms and cross terms in this entry, leaving
the root-coroot pairing. This argument uses neither ordered root coordinates
nor a Levi projection, and works over every Ree coefficient field.

The grading argument adapts the binary calculation in
`BinaryLocals/SuzukiProjection/SplitFactorization/Separation.lean`.
Source: the root calculation underlying Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.Parabolics.SeedGeneration.SuzukiWitness
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction LargeLocalSeeds Subgroup
noncomputable section

private def rootDegree (v : Fin 4 → ℤ) (r : F4Chevalley.Root) : ℤ :=
  v 0 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  v 1 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  v 2 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  v 3 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)
private def basisDegree (v : Fin 4 → ℤ) (a : F4Chevalley.BasisIndex) : ℤ :=
  v 0 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  v 1 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  v 2 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  v 3 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)
private theorem basisDegree_cartan (v : Fin 4 → ℤ) (j : typeF4RootPairing_base.support) :
    basisDegree v (Sum.inl j) = 0 := by simp [basisDegree, chevalleyBasisWeight]
private theorem basisDegree_root (v : Fin 4 → ℤ) (r : F4Chevalley.Root) :
    basisDegree v (Sum.inr r) = rootDegree v r := rfl

private theorem dividedPower_degree (v : Fin 4 → ℤ) (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree v i - basisDegree v j = (n : ℤ) * rootDegree v r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination v 0 * h0 + v 1 * h1 + v 2 * h2 + v 3 * h3

section Matrices
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
private def Raises (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0
omit [Fintype ι] [DecidableEq ι] in
private theorem raises_add {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]
omit [DecidableEq ι] in
private theorem raises_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i ≤ w k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]
private theorem raises_unit_mul {w : ι → ℤ} {A B : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (hB : Raises w (B.val - 1)) :
    Raises w ((A * B).val - 1) := by
  have he : (A * B).val - 1 = (A.val - 1) + (B.val - 1) +
      (A.val - 1) * (B.val - 1) := by simp only [Units.val_mul]; noncomm_ring
  rw [he]
  exact raises_add (raises_add hA hB) (raises_mul hA hB)
private theorem raises_unit_pow {w : ι → ℤ} {A : (Matrix ι ι K)ˣ}
    (hA : Raises w (A.val - 1)) (n : ℕ) : Raises w ((A ^ n).val - 1) := by
  induction n with
  | zero => intro i j _; simp
  | succ n ih => rw [pow_succ]; exact raises_unit_mul ih hA
end Matrices

private theorem specialized_zero (m : ℕ) (v : Fin 4 → ℤ) (r : F4Chevalley.Root)
    (n : ℕ) (i j : F4Chevalley.BasisIndex)
    (h : basisDegree v i - basisDegree v j ≠ (n : ℤ) * rootDegree v r) :
    specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n) i j = 0 := by
  have he : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
    by_contra hn
    exact h (dividedPower_degree v r n i j hn)
  simp [specializeMatrix, he]

private theorem dividedPower_raises (m : ℕ) (v : Fin 4 → ℤ) (r : F4Chevalley.Root)
    (hr : 0 < rootDegree v r) (n : ℕ) (hn : 0 < n) :
    Raises (basisDegree v) (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  apply specialized_zero m v r n i j
  have hp : 0 < (n : ℤ) * rootDegree v r := mul_pos (by exact_mod_cast hn) hr
  omega

private theorem rootCurve_raises (m : ℕ) (v : Fin 4 → ℤ) (r : F4Chevalley.Root)
    (hr : 0 < rootDegree v r) (t : CoefficientField m) :
    Raises (basisDegree v) ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises (basisDegree v) (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul,
      dividedPower_raises m v r hr n hn i j hij, mul_zero]
  have he : (1 + t • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private def outerWeight : Fin 4 → ℤ := ![4, 7, 5, 3]
private theorem outerDegree_eq (r : F4Chevalley.Root) :
    (rootDegree outerWeight r : ℝ) =
      typeF4SimpleCoefficient r.val 0 + typeF4SimpleCoefficient r.val 3 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) := by
    exact (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  simp only [rootDegree, outerWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Int.cast_add, Int.cast_mul, Int.cast_ofNat, hp,
    typeF4CorootScale_simpleRoot]
  norm_num [typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem simpleCoefficient_nonneg {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (q : Fin 4) :
    0 ≤ typeF4SimpleCoefficient r.val q := by
  have hs (r : F4Chevalley.Root) (hr : r ∈ typeF4RootPairing_base.support) :
      0 ≤ typeF4SimpleCoefficient r.val q := by
    obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective ⟨r, hr⟩
    have he : typeF4SimpleRootIndex i = r := congrArg Subtype.val hi
    rw [← he]
    fin_cases i <;> fin_cases q <;>
      norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val, typeF4SimpleRoot,
        basisVector, Matrix.cons_val_two, Matrix.cons_val_three]
  apply hr.induction_on_add hs
  intro i j k hk hi hj
  have hj' := hs j hj
  have hv : k.val = i.val + j.val := hk
  have he : typeF4SimpleCoefficient k.val q =
      typeF4SimpleCoefficient i.val q + typeF4SimpleCoefficient j.val q := by
    rw [hv]
    fin_cases q <;> simp [typeF4SimpleCoefficient, Pi.add_apply] <;> ring
  rw [he]
  exact add_nonneg hi hj'

private theorem outerDegree_radical {r : F4Chevalley.Root} (hr : IsRadicalRoot .suzuki r) :
    0 < rootDegree outerWeight r := by
  have h0 := simpleCoefficient_nonneg hr.1 0
  have h3 := simpleCoefficient_nonneg hr.1 3
  have hreal : 0 < (rootDegree outerWeight r : ℝ) := by
    rw [outerDegree_eq]
    obtain ⟨i, hi, hn⟩ := hr.2
    fin_cases i <;> simp [leviNodes] at hi
    · have := lt_of_le_of_ne h0 (Ne.symm hn)
      linarith
    · have := lt_of_le_of_ne h3 (Ne.symm hn)
      linarith
  exact_mod_cast hreal

private theorem finite_inv_eq_pow (m : ℕ) (x : SplitGroup m) :
    x⁻¹ = x ^ (orderOf x - 1) := by
  apply mul_left_cancel (a := x)
  rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]

private theorem radical_raises (m : ℕ) (x : SplitGroup m)
    (hx : x ∈ splitRadical m .suzuki) : Raises (basisDegree outerWeight) (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises m outerWeight r (outerDegree_radical hr) t
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    rw [finite_inv_eq_pow]
    exact raises_unit_pow hx _

private theorem dividedPower_one_cartan (m : ℕ) (s r : F4Chevalley.Root)
    (j : typeF4RootPairing_base.support) :
    specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower s 1) (Sum.inr r) (Sum.inl j) =
      if r = s then (typeF4RootPairing.pairingIn ℤ s j : CoefficientField m) else 0 := by
  classical
  have h := congrFun
    (WordRelations.Faithfulness.Adjoint.PositiveSimple.coordinateOperator_mulVec_cartan m s j)
    (Sum.inr r)
  rw [Matrix.mulVec_single_one] at h
  simpa [F4Chevalley.dividedPower_one, specializeMatrix,
    WordRelations.Faithfulness.Adjoint.coordinateOperator, Pi.single_apply] using h

private theorem two_root_entry (m : ℕ) (v : Fin 4 → ℤ) (r s : F4Chevalley.Root)
    (hr : rootDegree v r = 1) (hs : rootDegree v s = 1) (hne : r ≠ s)
    (j : typeF4RootPairing_base.support) :
    (rootGeneratorInGroup m r 1 * rootGeneratorInGroup m s 1).val.val
        (Sum.inr r) (Sum.inl j) =
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) := by
  classical
  let R := (F4Chevalley.rootCurve r (1 : CoefficientField m)).val
  let S := (F4Chevalley.rootCurve s (1 : CoefficientField m)).val
  have hR : Raises (basisDegree v) (R - 1) := rootCurve_raises m v r (by omega) 1
  have hS : Raises (basisDegree v) (S - 1) := rootCurve_raises m v s (by omega) 1
  have hcross : ((R - 1) * (S - 1)) (Sum.inr r) (Sum.inl j) = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : 1 ≤ basisDegree v k
    · rw [hR _ k (by rw [basisDegree_root, hr]; exact hk), zero_mul]
    · rw [hS k _ (by rw [basisDegree_cartan]; omega), mul_zero]
  have hentry (q : F4Chevalley.Root) (hq : rootDegree v q = 1) :
      (F4Chevalley.rootCurve q (1 : CoefficientField m)).val (Sum.inr r) (Sum.inl j) =
        if r = q then (typeF4RootPairing.pairingIn ℤ q j : CoefficientField m) else 0 := by
    have hn (n : ℕ) (hn : 2 ≤ n) :
        specializeMatrix (S := CoefficientField m)
          (F4Chevalley.integralOperators.rootDividedPower q n) (Sum.inr r) (Sum.inl j) = 0 := by
      apply specialized_zero m v q n
      rw [basisDegree_root, basisDegree_cartan, hr, hq]
      omega
    simp only [F4Chevalley.rootCurve_matrix_formula, Matrix.add_apply,
      one_smul, one_pow, hn 2 (by decide), hn 3 (by decide),
      dividedPower_one_cartan, Matrix.one_apply, reduceCtorEq, if_false,
      zero_add, add_zero]
  have he : R * S - 1 = (R - 1) + (S - 1) + (R - 1) * (S - 1) := by noncomm_ring
  have he' := congrArg (fun M => M (Sum.inr r) (Sum.inl j)) he
  change (R * S) (Sum.inr r) (Sum.inl j) = _
  simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, reduceCtorEq,
    if_false, sub_zero, hcross, R, S, hentry r hr, hentry s hs,
    if_pos rfl, if_neg hne, if_true, add_zero] using he'

private def detectingWeight : Fin 4 → ℤ := ![-1, 0, 0, 0]

private theorem middle_pairing_zero (r : F4Chevalley.Root) (h : r = gamma ∨ r = delta) :
    typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) = -1 := by
  have he : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) : ℝ) = -1 := by
    change algebraMap ℤ ℝ (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0)) = -1
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
      typeF4CorootScale_simpleRoot]
    rcases h with rfl | rfl
    all_goals norm_num [gamma_val, delta_val, alpha, beta, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
      Matrix.cons_val_two, Matrix.cons_val_three]
  exact_mod_cast he

private theorem detectingDegree (r : F4Chevalley.Root) (h : r = gamma ∨ r = delta) :
    rootDegree detectingWeight r = 1 := by
  simp [rootDegree, detectingWeight, middle_pairing_zero r h]

private theorem gamma_ne_delta : gamma ≠ delta := by
  intro h
  have he := congrArg (fun r : F4Chevalley.Root => r.val 3) h
  norm_num [gamma_val, delta_val, alpha, beta, typeF4SimpleRootIndex_val,
    typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three] at he

private theorem outerDegree_gamma : rootDegree outerWeight gamma = 0 := by
  have he := outerDegree_eq gamma
  norm_num [gamma_val, alpha, beta, typeF4SimpleRootIndex_val, typeF4SimpleRoot,
    typeF4SimpleCoefficient, Matrix.cons_val_two, Matrix.cons_val_three] at he
  exact_mod_cast he

/-- A Cartan column detects the central pair over every Ree coefficient field. -/
theorem centralWord_entry (m : ℕ) :
    (rootGeneratorInGroup m gamma 1 * rootGeneratorInGroup m delta 1).val.val
      (Sum.inr gamma) (Sum.inl (typeF4RootPairing_baseEquiv 0)) = 1 := by
  rw [two_root_entry m detectingWeight gamma delta (detectingDegree gamma (Or.inl rfl))
    (detectingDegree delta (Or.inr rfl)) gamma_ne_delta,
    typeF4RootPairing_baseEquiv_val, middle_pairing_zero gamma (Or.inl rfl)]
  simp [CharTwo.neg_eq]

/-- The central pair survives the root-defined Suzuki radical, including at q = 2. -/
theorem centralWord_not_mem_radical (m : ℕ) :
    rootGeneratorInGroup m gamma 1 * rootGeneratorInGroup m delta 1 ∉
      splitRadical m .suzuki := by
  intro h
  have he := radical_raises m _ h (Sum.inr gamma) (Sum.inl (typeF4RootPairing_baseEquiv 0))
    (by rw [basisDegree_root, basisDegree_cartan, outerDegree_gamma])
  have hn : (1 : CoefficientField m) = 0 := by
    simpa only [Matrix.sub_apply, Matrix.one_apply, reduceCtorEq, if_false,
      sub_zero, centralWord_entry] using he
  exact one_ne_zero hn

end
end ReeF4.Parabolics.SeedGeneration.SuzukiWitness
