module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Generation
/-!
# The linear radical and Levi have trivial matrix intersection

Grade the Cartan-plus-root basis using the simple coroots with coefficients
`(7, 14, 10, 5)`. This is the sum of the two middle simple-root coefficients:
it is positive on radical roots and zero on the four signed end roots.
Homogeneity of the integral divided powers makes radical matrices strictly
raise this grading away from the identity, while Levi matrices preserve it.
Their intersection therefore consists only of the identity matrix.

This extends the grading method of `LargeLocalSeeds/FixedGeometry/PositiveTwoGroup`
to the parabolic grading. It proves disjointness of the actual root-generated
subgroups without any assumption of relative normality or any order calculation.

Source: the standard F₄ root Levi construction underlying Aschbacher–Smith,
F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.BinaryLinear
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Subgroup
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
private def rootDegree (r : F4Chevalley.Root) : ℤ :=
  7 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  14 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  10 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  5 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)
private theorem rootDegree_simple (i : Fin 4) :
    rootDegree (typeF4SimpleRootIndex i) = if i = 0 ∨ i = 3 then 0 else 1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [rootDegree, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]
private theorem rootDegree_add {i j k : F4Chevalley.Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    rootDegree k = rootDegree i + rootDegree j := by
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ k q =
      typeF4RootPairing.pairingIn ℤ i q + typeF4RootPairing.pairingIn ℤ j q := by
    simpa using typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ)
      (j := q) (show typeF4RootPairing.root k =
        (1 : ℤ) • typeF4RootPairing.root i + (1 : ℤ) • typeF4RootPairing.root j by simpa using h)
  simp only [rootDegree, hp]
  ring
private theorem coefficient_add (x y : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (x + y) i =
      typeF4SimpleCoefficient x i + typeF4SimpleCoefficient y i := by
  fin_cases i <;> simp only [typeF4SimpleCoefficient, Pi.add_apply] <;> ring
private theorem rootDegree_nonneg_and_zero {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) :
    0 ≤ rootDegree r ∧ (rootDegree r = 0 →
      typeF4SimpleCoefficient r.val 1 = 0 ∧ typeF4SimpleCoefficient r.val 2 = 0) := by
  have hs (i : F4Chevalley.Root) (hi : i ∈ typeF4RootPairing_base.support) :
      0 ≤ rootDegree i ∧ (rootDegree i = 0 →
        typeF4SimpleCoefficient i.val 1 = 0 ∧ typeF4SimpleCoefficient i.val 2 = 0) := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, rootDegree_simple]
    fin_cases j <;> norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val, typeF4SimpleRoot, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three]
  apply hr.induction_on_add
  · exact hs
  · intro i j k hk hi hj
    have hjs := hs j hj
    rw [rootDegree_add hk]
    refine ⟨add_nonneg hi.1 hjs.1, ?_⟩
    intro he
    have hi0 := hi.2 (by omega)
    have hj0 := hjs.2 (by omega)
    change k.val = i.val + j.val at hk
    rw [hk, coefficient_add, coefficient_add, hi0.1, hi0.2, hj0.1, hj0.2]
    exact ⟨zero_add 0, zero_add 0⟩
private theorem rootDegree_radical {r : F4Chevalley.Root}
    (hr : IsRadicalRoot .linear r) : 0 < rootDegree r := by
  have h := rootDegree_nonneg_and_zero hr.1
  by_contra hn
  obtain ⟨h1, h2⟩ := h.2 (by omega)
  obtain ⟨i, hi, hc⟩ := hr.2
  fin_cases i
  · exact hi (by simp [leviNodes])
  · exact hc h1
  · exact hc h2
  · exact hi (by simp [leviNodes])
private theorem rootDegree_neg (r : F4Chevalley.Root) : rootDegree (-r) = -rootDegree r := by
  simp only [rootDegree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left]
  ring
private theorem rootDegree_levi {r : F4Chevalley.Root} (hr : IsLeviRoot r) :
    rootDegree r = 0 := by
  rcases hr with ⟨i, hi, rfl | rfl⟩
  all_goals have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
  · simp only [rootDegree_simple, if_pos hi']
  · simp only [rootDegree_neg, rootDegree_simple, if_pos hi', neg_zero]

/-- A positive root with a nonzero middle coefficient is not a Levi root. -/
theorem isRadicalRoot_not_isLeviRoot {r : F4Chevalley.Root}
    (hr : IsRadicalRoot .linear r) : ¬ IsLeviRoot r := by
  intro hl
  have hpos := rootDegree_radical hr
  rw [rootDegree_levi hl] at hpos
  exact (lt_irrefl 0) hpos

private def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  7 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  14 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  10 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  5 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * rootDegree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  dsimp only [basisDegree, rootDegree]
  linear_combination 7 * h0 + 14 * h1 + 10 * h2 + 5 * h3

section Matrices
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
private def Raises (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0
private def Preserves (w : ι → ℤ) (A : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≠ w j → A i j = 0
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
omit [Fintype ι] [DecidableEq ι] in
private theorem preserves_add {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Preserves w A) (hB : Preserves w B) : Preserves w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]
omit [DecidableEq ι] in
private theorem preserves_mul {w : ι → ℤ} {A B : Matrix ι ι K}
    (hA : Preserves w A) (hB : Preserves w B) : Preserves w (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : w i = w k
  · rw [hB k j (by omega), mul_zero]
  · rw [hA i k hik, zero_mul]
omit [Fintype ι] in
private theorem preserves_one (w : ι → ℤ) : Preserves w (1 : Matrix ι ι K) := by
  intro i j hij
  exact Matrix.one_apply_ne (fun he => hij (congrArg w he))
private theorem preserves_pow {w : ι → ℤ} {A : Matrix ι ι K}
    (hA : Preserves w A) (n : ℕ) : Preserves w (A ^ n) := by
  induction n with
  | zero => exact preserves_one w
  | succ n ih => rw [pow_succ]; exact preserves_mul ih hA
end Matrices

private theorem dividedPower_raises (m : ℕ) (r : F4Chevalley.Root)
    (hr : 0 < rootDegree r) (n : ℕ) (hn : 0 < n) :
    Raises basisDegree (specializeMatrix (S := CoefficientField m)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hp : 0 < (n : ℤ) * rootDegree r := mul_pos (by exact_mod_cast hn) hr
  omega

private theorem rootCurve_raises (m : ℕ) (r : F4Chevalley.Root)
    (hr : 0 < rootDegree r) (t : CoefficientField m) :
    Raises basisDegree ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Raises basisDegree (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul,
      dividedPower_raises m r hr n hn i j hij, mul_zero]
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

private theorem rootCurve_preserves (m : ℕ) (r : F4Chevalley.Root)
    (hr : rootDegree r = 0) (t : CoefficientField m) :
    Preserves basisDegree (F4Chevalley.rootCurve r t).val := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (s : CoefficientField m) :
      Preserves basisDegree (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have he : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have h := dividedPower_degree r n i j hne
      rw [hr, mul_zero] at h
      exact hij (sub_eq_zero.mp h)
    simp [Matrix.smul_apply, specializeMatrix, he]
  exact preserves_add (preserves_add (preserves_add (preserves_one _)
    (hs 1 t)) (hs 2 (t ^ 2))) (hs 3 (t ^ 3))

private theorem finite_inv_eq_pow (m : ℕ) (x : SplitGroup m) :
    x⁻¹ = x ^ (orderOf x - 1) := by
  apply mul_left_cancel (a := x)
  rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]

private theorem radical_raises (m : ℕ) (x : SplitGroup m)
    (hx : x ∈ splitRadical m .linear) : Raises basisDegree (x.val.val - 1) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_raises m r (rootDegree_radical hr) t
  | one => intro i j _; simp
  | mul x y _ _ hx hy => exact raises_unit_mul hx hy
  | inv x _ hx =>
    rw [finite_inv_eq_pow]
    exact raises_unit_pow hx _

private theorem levi_preserves (m : ℕ) (x : SplitGroup m)
    (hx : x ∈ splitLevi m) : Preserves basisDegree x.val.val := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact rootCurve_preserves m r (rootDegree_levi hr) t
  | one => exact preserves_one _
  | mul x y _ _ hx hy => exact preserves_mul hx hy
  | inv x _ hx =>
    rw [finite_inv_eq_pow]
    exact preserves_pow hx _

/-- The root-defined radical intersects the actual end-node Levi trivially. -/
theorem splitRadical_disjoint_splitLevi (m : ℕ) :
    Disjoint (splitRadical m .linear) (splitLevi m) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  have hp := radical_raises m x hx
  have hl := levi_preserves m x hy
  apply Subtype.ext
  apply Units.ext
  change x.val.val = 1
  apply sub_eq_zero.mp
  ext i j
  by_cases hij : basisDegree i ≤ basisDegree j
  · exact hp i j hij
  · have hne : basisDegree i ≠ basisDegree j := by omega
    have hij' : i ≠ j := fun he => hne (congrArg basisDegree he)
    simp only [Matrix.sub_apply, hl i j hne, Matrix.one_apply_ne hij', sub_self,
      Matrix.zero_apply]

end ReeF4.Parabolics.BinaryLinear
