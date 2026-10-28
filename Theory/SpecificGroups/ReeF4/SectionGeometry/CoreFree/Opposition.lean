module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Opposition separates the linear Ree radical

The sixth power of the parameter-one Coxeter word is the longest-Weyl
representative. Its already proved matrix formula and exceptional-twist
invariance place it in the actual Ree fixed group.

Grade the Cartan-plus-root basis by the coroot combination `(7,14,10,5)`.
On roots this is the sum of the coefficients at the two middle nodes, so
linear radical roots have positive degree and the end-node Levi has degree
zero. Divided-power homogeneity makes radical matrices strictly raise this
grade; conjugation by opposition makes them strictly lower it. The full
parabolic weakly raises the grade, including its diagonal coroot torus.
An element satisfying both matrix conditions is identity. Faithful inclusion
then descends the intersection statement to the actual exceptional fixed group.

The grading argument adapts `FixedCollection/SeedGeneration/Separation.lean`.
Source: GLS3, Theorem 2.3.5 and the Levi decomposition of Theorem 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.Opposition
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open RootPairing.IntegralGeckConstruction LargeLocalSeeds Parabolics
open LocalBlockInput.PairNormalization
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

private def coefficients : Fin 4 → ℤ := ![7, 14, 10, 5]

private def degree (r : F4Chevalley.Root) : ℤ :=
  ∑ i : Fin 4, coefficients i *
    typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)

private theorem degree_eq (r : F4Chevalley.Root) :
    (degree r : ℝ) =
      typeF4SimpleCoefficient r.val 1 + typeF4SimpleCoefficient r.val 2 := by
  have hp (i : Fin 4) : (typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) : ℝ) =
      typeF4CorootScale (typeF4SimpleRootIndex i) * dot r.val (typeF4SimpleRoot i) := by
    exact (typeF4RootPairing.algebraMap_pairingIn ℤ r (typeF4SimpleRootIndex i)).trans
      (typeF4RootPairing_pairing r (typeF4SimpleRootIndex i))
  simp only [degree, Int.cast_sum, Int.cast_mul, hp, typeF4CorootScale_simpleRoot]
  norm_num [coefficients, Fin.sum_univ_four,
      typeF4SimpleCoefficient, dot, typeF4SimpleRoot, basisVector,
      Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem coefficient_nonneg {r : F4Chevalley.Root}
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

private theorem degree_radical {r : F4Chevalley.Root} (hr : IsRadicalRoot .linear r) :
    0 < degree r := by
  have hp (i : Fin 4) := coefficient_nonneg hr.1 i
  have hreal : 0 < (degree r : ℝ) := by
    rw [degree_eq]
    obtain ⟨i, hi, hn⟩ := hr.2
    fin_cases i <;> simp [leviNodes] at hi
    · have := lt_of_le_of_ne (hp 1) (Ne.symm hn)
      linarith [hp 2]
    · have := lt_of_le_of_ne (hp 2) (Ne.symm hn)
      linarith [hp 1]
  exact_mod_cast hreal

private def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  ∑ i : Fin 4, coefficients i *
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex i)

private theorem dividedPower_degree (r : F4Chevalley.Root) (n : ℕ)
    (i j : F4Chevalley.BasisIndex)
    (hij : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0) :
    basisDegree i - basisDegree j = (n : ℤ) * degree r := by
  have h := rootDividedPower_isChevalleyHomogeneous (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r n i j hij
  have h0 := h (typeF4SimpleRootIndex 0)
  have h1 := h (typeF4SimpleRootIndex 1)
  have h2 := h (typeF4SimpleRootIndex 2)
  have h3 := h (typeF4SimpleRootIndex 3)
  simp only [basisDegree, degree, Fin.sum_univ_four]
  linear_combination coefficients 0 * h0 + coefficients 1 * h1 +
    coefficients 2 * h2 + coefficients 3 * h3

private theorem degree_nonneg {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 ≤ degree r := by
  have h : 0 ≤ (degree r : ℝ) := by
    rw [degree_eq]
    exact add_nonneg (coefficient_nonneg hr 1) (coefficient_nonneg hr 2)
  exact_mod_cast h

private theorem degree_neg (r : F4Chevalley.Root) : degree (-r) = -degree r := by
  simp only [degree, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left, mul_neg, Finset.sum_neg_distrib]

private theorem degree_simple (i : Fin 4) :
    degree (typeF4SimpleRootIndex i) = if i = 0 ∨ i = 3 then 0 else 1 := by
  have h : (degree (typeF4SimpleRootIndex i) : ℝ) =
      if i = 0 ∨ i = 3 then 0 else 1 := by
    rw [degree_eq]
    fin_cases i <;> norm_num [typeF4SimpleCoefficient, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, basisVector, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]
  exact_mod_cast h

private theorem degree_seed {r : F4Chevalley.Root}
    (hr : IsSeedRoot .linear r) : 0 ≤ degree r := by
  rcases hr with hr | ⟨i, hi, rfl⟩
  · exact degree_nonneg hr
  · have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
    rw [degree_neg, degree_simple, if_pos hi', neg_zero]

/-- Strictly lowering matrices, used on the difference from identity. -/
private def Lowers (A : MatrixCarrier m) : Prop :=
  ∀ i j, basisDegree j ≤ basisDegree i → A i j = 0

/-- Weakly raising matrices, allowing the entire degree-zero Levi. -/
private def Nondecreasing (A : MatrixCarrier m) : Prop :=
  ∀ i j, basisDegree i < basisDegree j → A i j = 0

private theorem lowers_add {A B : MatrixCarrier m} (hA : Lowers A) (hB : Lowers B) :
    Lowers (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem lowers_mul {A B : MatrixCarrier m} (hA : Lowers A) (hB : Lowers B) :
    Lowers (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree k ≤ basisDegree i
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem lowers_unit_mul {x y : SplitGroup m}
    (hx : Lowers (x.val.val - 1)) (hy : Lowers (y.val.val - 1)) :
    Lowers ((x * y).val.val - 1) := by
  have he : (x * y).val.val - 1 = (x.val.val - 1) + (y.val.val - 1) +
      (x.val.val - 1) * (y.val.val - 1) := by
    change x.val.val * y.val.val - 1 = _
    noncomm_ring
  rw [he]
  exact lowers_add (lowers_add hx hy) (lowers_mul hx hy)

private theorem nondecreasing_one : Nondecreasing (1 : MatrixCarrier m) := by
  intro i j hij
  have hne : i ≠ j := fun he => (ne_of_lt hij) (congrArg basisDegree he)
  simp [hne]

private theorem nondecreasing_add {A B : MatrixCarrier m}
    (hA : Nondecreasing A) (hB : Nondecreasing B) : Nondecreasing (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private theorem nondecreasing_mul {A B : MatrixCarrier m}
    (hA : Nondecreasing A) (hB : Nondecreasing B) : Nondecreasing (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : basisDegree i < basisDegree k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

private theorem property_inv {p : SplitGroup m → Prop} (hone : p 1)
    (hmul : ∀ x y, p x → p y → p (x * y)) {x : SplitGroup m} (hx : p x) : p x⁻¹ := by
  have hp (n : ℕ) : p (x ^ n) := by
    induction n with
    | zero => simpa only [pow_zero] using hone
    | succ n ih => simpa only [pow_succ] using hmul (x ^ n) x ih hx
  obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
  have hinv : x⁻¹ = x ^ (n - 1) := by
    apply mul_left_cancel (a := x)
    rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hn, he]
  rw [hinv]
  exact hp _

private def nondecreasingSubgroup (m : ℕ) : Subgroup (SplitGroup m) where
  carrier := {x | Nondecreasing x.val.val}
  one_mem' := nondecreasing_one
  mul_mem' := nondecreasing_mul
  inv_mem' := property_inv nondecreasing_one (fun _ _ => nondecreasing_mul)

private theorem rootCurve_nondecreasing (r : F4Chevalley.Root)
    (hr : 0 ≤ degree r) (t : CoefficientField m) :
    Nondecreasing (F4Chevalley.rootCurve r t).val := by
  have hs (n : ℕ) (s : CoefficientField m) :
      Nondecreasing (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      have hp : 0 ≤ (n : ℤ) * degree r := mul_nonneg (by omega) hr
      omega
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
  exact nondecreasing_add (nondecreasing_add (nondecreasing_add nondecreasing_one (hs 1 t))
    (hs 2 (t ^ 2))) (hs 3 (t ^ 3))

private theorem rootCurve_lowers (r : F4Chevalley.Root)
    (hr : degree r < 0) (t : CoefficientField m) :
    Lowers ((F4Chevalley.rootCurve r t).val - 1) := by
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField m) :
      Lowers (s • specializeMatrix (S := CoefficientField m)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    have hz : F4Chevalley.integralOperators.rootDividedPower r n i j = 0 := by
      by_contra hne
      have hd := dividedPower_degree r n i j hne
      have hp : (n : ℤ) * degree r < 0 := mul_neg_of_pos_of_neg (by omega) hr
      omega
    simp [specializeMatrix, hz]
  rw [F4Chevalley.rootCurve_matrix_formula]
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
  exact lowers_add (lowers_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private theorem parabolic_nondecreasing :
    splitParabolic m .linear ≤ nondecreasingSubgroup m := by
  apply sup_le
  · apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    exact rootCurve_nondecreasing r (degree_seed hr) t
  · rw [splitTorus_eq_diagonalTorus]
    intro x hx
    obtain ⟨u, hu⟩ := hx
    change diagonalTorusHom m u = x.val at hu
    change Nondecreasing x.val.val
    rw [← hu, diagonalTorusHom_apply, F4Chevalley.torusConjugation.torusElement_apply]
    change Nondecreasing (Matrix.diagonal _)
    intro i j hij
    have hne : i ≠ j := fun he => (ne_of_lt hij) (congrArg basisDegree he)
    exact Matrix.diagonal_apply_ne _ hne

private theorem radical_opposition_lowers (x : SplitGroup m)
    (hx : x ∈ splitRadical m .linear) :
    Lowers (((MulAut.conj (splitOpposition m)) x).val.val - 1) := by
  have hone : Lowers ((1 : SplitGroup m).val.val - 1) := by intro i j _; simp
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    simp only [MulAut.conj_apply, splitOpposition_conj_root]
    apply rootCurve_lowers
    rw [degree_neg]
    exact neg_neg_of_pos (degree_radical hr)
  | one => simpa only [map_one] using hone
  | mul x y _ _ hx hy => simpa only [map_mul] using lowers_unit_mul hx hy
  | inv x _ hx =>
    simpa only [map_inv] using
      (property_inv (p := fun y => Lowers (y.val.val - 1))
        hone (fun _ _ => lowers_unit_mul) hx)

/-- The actual split linear radical meets the opposite full parabolic trivially,
including the complementary coroot torus. -/
theorem split_linear_radical_disjoint_opposite_parabolic (m : ℕ) :
    Disjoint (splitRadical m .linear)
      ((splitParabolic m .linear).comap (MulAut.conj (splitOpposition m)).toMonoidHom) := by
  apply disjoint_def.mpr
  intro x hxR hxP
  have hR := radical_opposition_lowers x hxR
  have hP := parabolic_nondecreasing hxP
  change Nondecreasing (((MulAut.conj (splitOpposition m)) x).val.val) at hP
  have he : (MulAut.conj (splitOpposition m)) x = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : basisDegree j ≤ basisDegree i
    · exact sub_eq_zero.mp (hR i j hij)
    · have hlt := lt_of_not_ge hij
      have hne : i ≠ j := fun he => (ne_of_lt hlt) (congrArg basisDegree he)
      exact (hP i j hlt).trans (by simp [hne])
  exact (MulAut.conj (splitOpposition m)).injective (he.trans (map_one _).symm)

/-- The genuine longest-Weyl representative in the exceptional fixed group. -/
def linearOpposition (m : ℕ) : Model m :=
  ⟨splitOpposition m, by
    apply (mem_fixedSubgroup m _).mpr
    simpa only [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism,
      ← reeAutomorphism_apply] using twist_splitOpposition (canonicalLocalBlockInput m)⟩

@[simp] theorem toSplitGroup_linearOpposition (m : ℕ) :
    toSplitGroup m (linearOpposition m) = splitOpposition m := by
  rw [toSplitGroup_apply]
  rfl

/-- Faithful inclusion descends the split intersection to the actual Ree carrier.
The comap means exactly that `g * x * g⁻¹` belongs to the full parabolic. -/
theorem linear_radical_disjoint_opposite_parabolic (m : ℕ) :
    Disjoint (radical m .linear)
      ((parabolic m .linear).comap (MulAut.conj (linearOpposition m)).toMonoidHom) := by
  apply disjoint_def.mpr
  intro x hxR hxP
  apply toSplitGroup_injective m
  rw [map_one]
  apply (disjoint_def.mp (split_linear_radical_disjoint_opposite_parabolic m)) hxR
  change toSplitGroup m (linearOpposition m * x * (linearOpposition m)⁻¹) ∈
    splitParabolic m .linear at hxP
  simpa only [map_mul, map_inv, toSplitGroup_linearOpposition,
    mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxP

/-- In particular this supplies the opposition input for every large Ree group
(`1 ≤ m`); the matrix proof also covers the full binary fixed group. -/
theorem exists_linear_opposition (m : ℕ) :
    ∃ g : Model m, Disjoint (radical m .linear)
      ((parabolic m .linear).comap (MulAut.conj g).toMonoidHom) :=
  ⟨linearOpposition m, linear_radical_disjoint_opposite_parabolic m⟩

end ReeF4.SectionGeometry.Opposition
