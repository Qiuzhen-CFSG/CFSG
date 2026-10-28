module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.Coordinates

/-!
# Positive matrix support in the binary Ree group

Every positive root curve strictly raises the integral root-height grading
away from its identity term. Products and inverses of the generators therefore
preserve the sum of the Cartan and positive-root spaces. In particular a fixed
positive element cannot send a Cartan vector to a vector with a negative-root
coordinate.

The grading calculation follows `LargeLocalSeeds.FixedGeometry.PositiveTwoGroup`;
we prove the support consequence here without changing that shared module.
Source: the homogeneous integral Chevalley divided powers, as in Steinberg,
*Lectures on Chevalley Groups*.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction LargeLocalSeeds
open scoped Matrix

private def Raises (w : F4Chevalley.BasisIndex → ℤ) (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
    (CoefficientField 0)) : Prop :=
  ∀ i j, w i ≤ w j → A i j = 0

private theorem raises_add {w} {A B : Matrix F4Chevalley.BasisIndex
    F4Chevalley.BasisIndex (CoefficientField 0)}
    (hA : Raises w A) (hB : Raises w B) : Raises w (A + B) := by
  intro i j hij
  simp only [Matrix.add_apply, hA i j hij, hB i j hij, add_zero]

private noncomputable def rootDegree (r : F4Chevalley.Root) : ℤ :=
  11 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 0) +
  21 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 1) +
  15 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 2) +
  8 * typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex 3)

private theorem rootDegree_simple (i : Fin 4) : rootDegree (typeF4SimpleRootIndex i) = 1 := by
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

private theorem rootDegree_pos {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) : 0 < rootDegree r := by
  apply hr.induction_on_add
  · intro i hi
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, rootDegree_simple]
    omega
  · intro i j k hk hi hj
    obtain ⟨l, hl⟩ := typeF4RootPairing_baseEquiv.surjective ⟨j, hj⟩
    have he : typeF4SimpleRootIndex l = j := congrArg Subtype.val hl
    rw [rootDegree_add hk, ← he, rootDegree_simple]
    omega

private noncomputable def basisDegree (a : F4Chevalley.BasisIndex) : ℤ :=
  11 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 0) +
  21 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 1) +
  15 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 2) +
  8 * chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex 3)

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
  linear_combination 11 * h0 + 21 * h1 + 15 * h2 + 8 * h3

private theorem dividedPower_raises (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (n : ℕ) (hn : 0 < n) :
    Raises basisDegree (specializeMatrix (S := CoefficientField 0)
      (F4Chevalley.integralOperators.rootDividedPower r n)) := by
  intro i j hij
  by_contra hne
  have hint : F4Chevalley.integralOperators.rootDividedPower r n i j ≠ 0 := by
    intro he
    apply hne
    simp [specializeMatrix, he]
  have hd := dividedPower_degree r n i j hint
  have hp : 0 < (n : ℤ) * rootDegree r :=
    mul_pos (by exact_mod_cast hn) (rootDegree_pos hr)
  omega

private theorem rootCurve_raises (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField 0) :
    Raises basisDegree ((F4Chevalley.rootCurve r t).val - 1) := by
  rw [F4Chevalley.rootCurve_matrix_formula]
  have hs (n : ℕ) (hn : 0 < n) (s : CoefficientField 0) :
      Raises basisDegree (s • specializeMatrix (S := CoefficientField 0)
        (F4Chevalley.integralOperators.rootDividedPower r n)) := by
    intro i j hij
    simp only [Matrix.smul_apply, smul_eq_mul, dividedPower_raises r hr n hn i j hij,
      mul_zero]
  have he : (1 + t • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 3)) - 1 =
      t • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 1) +
      t ^ 2 • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 2) +
      t ^ 3 • specializeMatrix (S := CoefficientField 0) (F4Chevalley.integralOperators.rootDividedPower r 3) := by abel
  rw [he]
  exact raises_add (raises_add (hs 1 (by decide) t) (hs 2 (by decide) (t ^ 2)))
    (hs 3 (by decide) (t ^ 3))

private theorem rootDegree_neg (r : F4Chevalley.Root) :
    let := typeF4RootPairing.indexNeg
    rootDegree (-r) = -rootDegree r := by
  let := typeF4RootPairing.indexNeg
  have hp (q : F4Chevalley.Root) : typeF4RootPairing.pairingIn ℤ (-r) q =
      -typeF4RootPairing.pairingIn ℤ r q := by
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    rw [map_neg, typeF4RootPairing.algebraMap_pairingIn]
    simp only [← typeF4RootPairing.root_coroot_eq_pairing,
      typeF4RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self, LinearMap.neg_apply, map_neg]
    rw [typeF4RootPairing.algebraMap_pairingIn,
      typeF4RootPairing.root_coroot_eq_pairing]
  simp only [rootDegree, hp]
  ring

private theorem rootDegree_neg_of_not_pos (r : F4Chevalley.Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) : rootDegree r < 0 := by
  let := typeF4RootPairing.indexNeg
  have hp := rootDegree_pos ((RootPairing.Base.IsPos.neg_iff_not
    typeF4RootPairing_base r).mpr hr)
  rw [rootDegree_neg] at hp
  omega

private def NonnegativeSupport (v : F4Chevalley.BasisIndex → CoefficientField 0) : Prop :=
  ∀ i, basisDegree i < 0 → v i = 0

private theorem preserves_nonnegative_of_raises
    (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField 0))
    (hA : Raises basisDegree (A - 1))
    (v : F4Chevalley.BasisIndex → CoefficientField 0) (hv : NonnegativeSupport v) :
    NonnegativeSupport (A *ᵥ v) := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : basisDegree j < 0
  · rw [hv j hj, mul_zero]
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    have hz := hA i j (by omega)
    simp only [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at hz
    rw [hz, zero_mul]

private theorem split_preserves_nonnegative (x : SplitGroup 0)
    (hx : x ∈ splitUnipotent 0) :
    ∀ v, NonnegativeSupport v → NonnegativeSupport (x.val.val *ᵥ v) := by
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    exact preserves_nonnegative_of_raises _ (rootCurve_raises r hr t)
  | inv_mem x hx =>
    obtain ⟨r, t, hr, rfl⟩ := hx
    change ∀ v, NonnegativeSupport v →
      NonnegativeSupport ((F4Chevalley.rootCurve r t)⁻¹.val *ᵥ v)
    rw [F4Chevalley.rootCurve_inv]
    exact preserves_nonnegative_of_raises _ (rootCurve_raises r hr (-t))
  | one => intro v hv; simpa using hv
  | mul x y _ _ hx hy =>
    intro v hv
    simpa only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec] using hx _ (hy v hv)

/-- Positive matrices send Cartan vectors into Cartan plus positive-root space. -/
theorem unipotent_cartan_positive (x : Model 0) (hx : x ∈ unipotent 0)
    (v : F4Chevalley.BasisIndex → CoefficientField 0) (hv : CartanSupported v) :
    PositiveSupported (matrix x *ᵥ v) := by
  have hv' : NonnegativeSupport v := by
    intro i hi
    cases i with
    | inl j => simp [basisDegree, chevalleyBasisWeight] at hi
    | inr r => exact hv r
  have h := split_preserves_nonnegative (toSplitGroup 0 x) hx v hv'
  intro r hr
  exact h (Sum.inr r) (rootDegree_neg_of_not_pos r hr)

end ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
