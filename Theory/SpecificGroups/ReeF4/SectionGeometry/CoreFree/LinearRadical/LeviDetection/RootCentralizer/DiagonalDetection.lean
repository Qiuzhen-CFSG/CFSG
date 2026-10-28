module
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.RootCentralizer.FiniteCalculation
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.DividedPowers
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates

/-!
# Eliminating the diagonal centralizer inside the full Levi

The full end-node Levi fixes the first Cartan basis vector, including its
complementary torus. This fixes the first scalar of the two-value diagonal
centralizer. All split root generators have square one in characteristic two,
so their determinants, and hence all split-group determinants, are one.
The other scalar has cube one; the field order 2^(2m+1) excludes a nontrivial
cube root of unity. Thus the diagonal centralizer is trivial in the full Levi.

Source: the root-defined Levi in GLS3 Theorem 2.6.5(e,g),
`refs/KGroup/GLS3/chapter2.tex`, and the certified integral F₄ end-root tables.
-/

@[expose] public noncomputable section
namespace ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.Cartan.FieldSeparation.TraceValues
open Subgroup Parabolics LargeLocalSeeds Parabolics.Binary.FixedGeometry
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open scoped Matrix
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

lemma splitGroup_det (m : ℕ) (x : SplitGroup m) : x.val.val.det = 1 := by
  have hle : SplitGroup m ≤ (Matrix.GeneralLinearGroup.det).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨r, t⟩, rfl⟩
    change Matrix.GeneralLinearGroup.det (F4Chevalley.rootCurve r t) = 1
    apply Units.ext
    change (F4Chevalley.rootCurve r t).val.det = 1
    have he : (F4Chevalley.rootCurve r t).val * (F4Chevalley.rootCurve r t).val = 1 := by
      change (F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r t).val = _
      rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero, F4Chevalley.rootCurve_zero]
      rfl
    have hd := congrArg Matrix.det he
    rw [Matrix.det_mul, Matrix.det_one] at hd
    rcases mul_self_eq_one_iff.mp hd with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  exact congrArg Units.val (hle x.property)

lemma reindex_specialize {F : Type*} [CommRing F] (A : Matrix Basis Basis ℤ) :
    reindex (specializeMatrix (S := F) A) = (reindex A).map (Int.castRingHom F) := rfl
lemma reindex_smul {F : Type*} [CommRing F] (t : F) (A : Matrix Basis Basis F) :
    reindex (t • A) = t • reindex A := rfl

private lemma positive0Linear_even (i : Fin 52) : matrix positive0Linear i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma negative0Linear_even (i : Fin 52) : matrix negative0Linear i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma positive3Linear_even (i : Fin 52) : matrix positive3Linear i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma negative3Linear_even (i : Fin 52) : matrix negative3Linear i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma positive0Quadratic_even (i : Fin 52) : matrix positive0Quadratic i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma negative0Quadratic_even (i : Fin 52) : matrix negative0Quadratic i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma positive3Quadratic_even (i : Fin 52) : matrix positive3Quadratic i 0 % 2 = 0 := by
  revert i
  decide +kernel

private lemma negative3Quadratic_even (i : Fin 52) : matrix negative3Quadratic i 0 % 2 = 0 := by
  revert i
  decide +kernel

set_option linter.unusedSimpArgs false in
private lemma end_curve_column (m : ℕ) (j : Fin 4) (hj : j = 0 ∨ j = 3)
    (p : Bool) (t : CoefficientField m) (i : Fin 52) :
    reindex (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex j)) t).val.val i 0 =
      (1 : Matrix (Fin 52) (Fin 52) (CoefficientField m)) i 0 := by
  have hz (a : ℤ) (ha : a % 2 = 0) : (a : CoefficientField m) = 0 := by
    rw [CharTwo.intCast_eq_mod, ha, Int.cast_zero]
  have h0 := hz _ (positive0Linear_even i)
  have h1 := hz _ (negative0Linear_even i)
  have h2 := hz _ (positive3Linear_even i)
  have h3 := hz _ (negative3Linear_even i)
  have h4 := hz _ (positive0Quadratic_even i)
  have h5 := hz _ (negative0Quadratic_even i)
  have h6 := hz _ (positive3Quadratic_even i)
  have h7 := hz _ (negative3Quadratic_even i)
  change reindex (F4Chevalley.rootCurve _ t).val i 0 = _
  rw [F4Chevalley.rootCurve_matrix_formula]
  rcases hj with rfl | rfl <;> cases p
  all_goals
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
      ← typeF4RootPairing_baseEquiv_val, WordRelations.rootDividedPower_simple,
      WordRelations.rootDividedPower_neg_simple, map_add, map_one, reindex_smul,
      reindex_specialize, eDividedPower_one, fDividedPower_one,
      eMatrix_0, fMatrix_0, eMatrix_3, fMatrix_3,
      eDividedPower_0_two, fDividedPower_0_two, eDividedPower_3_two, fDividedPower_3_two,
      eDividedPower_0_three, fDividedPower_0_three, eDividedPower_3_three, fDividedPower_3_three,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Int.coe_castRingHom, Matrix.zero_apply, Int.cast_zero,
      h0, h1, h2, h3, h4, h5, h6, h7, mul_zero, add_zero]

private def cartanVector (m : ℕ) : F4Chevalley.BasisIndex → CoefficientField m :=
  Pi.single (basisEquiv 0) 1

private def fixesCartanSubgroup (m : ℕ) : Subgroup (SplitGroup m) where
  carrier := {x | x.val.val *ᵥ cartanVector m = cartanVector m}
  one_mem' := Matrix.one_mulVec _
  mul_mem' hx hy := by
    change (_ * _) *ᵥ cartanVector m = _
    rw [← Matrix.mulVec_mulVec, hy, hx]
  inv_mem' {x} hx := by
    change x⁻¹.val.val *ᵥ cartanVector m = _
    calc
      x⁻¹.val.val *ᵥ cartanVector m = x⁻¹.val.val *ᵥ (x.val.val *ᵥ cartanVector m) := by rw [hx]
      _ = cartanVector m := by
        rw [Matrix.mulVec_mulVec]
        change (x⁻¹ * x).val.val *ᵥ cartanVector m = _
        rw [inv_mul_cancel]
        exact Matrix.one_mulVec _

private lemma end_curve_fixes (m : ℕ) (j : Fin 4) (hj : j = 0 ∨ j = 3)
    (p : Bool) (t : CoefficientField m) :
    rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex j)) t ∈
      fixesCartanSubgroup m := by
  change _ *ᵥ Pi.single (basisEquiv 0) 1 = _
  rw [Matrix.mulVec_single_one]
  ext i
  obtain ⟨i, rfl⟩ := basisEquiv.surjective i
  simpa only [reindex_apply, Matrix.col_apply, cartanVector, Pi.single_apply, basisEquiv.injective.eq_iff,
    Matrix.one_apply] using end_curve_column m j hj p t i

lemma fullLevi_cartan_entry (m : ℕ) (l : Model m) (hl : l ∈ fullLevi m) :
    reindex (modelMatrix m l) 0 0 = 1 := by
  have hle : splitFullLevi m ≤ fixesCartanSubgroup m := by
    apply sup_le
    · apply sup_le <;> apply (closure_le _).mpr
      all_goals
        rintro _ ⟨r, t, hr, rfl⟩
        obtain ⟨j, hj, hrj⟩ := BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
          (hr.1 1 (by simp [leviNodes])) (hr.1 2 (by simp [leviNodes]))
        have hj' : j = 0 ∨ j = 3 := by simpa [leviNodes] using hj
        rcases hrj with rfl | rfl
        · exact end_curve_fixes m j hj' true t
        · exact end_curve_fixes m j hj' false t
    · rw [splitTorus_eq_diagonalTorus]
      intro x hx
      obtain ⟨u, hu⟩ := hx
      change diagonalTorusHom m u = x.val at hu
      change x.val.val *ᵥ cartanVector m = cartanVector m
      rw [← hu, diagonalTorusHom_apply, F4Chevalley.torusConjugation.torusElement_apply]
      change Matrix.diagonal _ *ᵥ Pi.single (Sum.inl (typeF4RootPairing_baseEquiv 0) : F4Chevalley.BasisIndex) 1 =
        Pi.single (Sum.inl (typeF4RootPairing_baseEquiv 0) : F4Chevalley.BasisIndex) 1
      rw [Matrix.mulVec_single_one]
      ext i
      by_cases hi : i = .inl (typeF4RootPairing_baseEquiv 0)
      · subst i
        simp [Matrix.col_apply, chevalleyBasisTorusUnit, chevalleyBasisWeight]
      · simp [Matrix.col_apply, hi]
  have h := congrFun (hle hl) (basisEquiv 0)
  simpa only [reindex_apply, modelMatrix, cartanVector, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_same] using h


/-- The odd extension degree of the Ree field excludes nontrivial cube roots. -/
lemma coefficient_cube_eq_one (m : ℕ) (b : CoefficientField m) (hb : b ^ 3 = 1) : b = 1 := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  let u : (CoefficientField m)ˣ := Units.mk0 b hb0
  have hu : u ^ 3 = 1 := Units.ext hb
  have hd3 := orderOf_dvd_of_pow_eq_one hu
  have hdq := orderOf_dvd_natCard u
  rw [Nat.card_units, field_card] at hdq
  have hfour : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod, hfour]
  have hsub : (2 ^ (2 * m + 1) - 1) % 3 = 1 := by
    generalize 2 ^ (2 * m + 1) = q at hq ⊢
    omega
  have hcop : Nat.Coprime 3 (2 ^ (2 * m + 1) - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hz := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hd := Nat.dvd_gcd hd3 hdq
  rw [hcop.gcd_eq_one] at hd
  have he : u = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hd)
  exact congrArg Units.val he

/-- The three exceptional coordinates contribute exactly a cube. -/
lemma diagonalShape_one_det {F : Type*} [CommRing F] (b : F) :
    (diagonalShape 1 b).det = b ^ 3 := by
  rw [diagonalShape, Matrix.det_diagonal, Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  congr 1

/-- The two-value diagonal shape is trivial on the actual full fixed Levi.
The Cartan column fixes the first scalar, and determinant one eliminates the
other using the odd degree of the coefficient field. -/
lemma modelMatrix_eq_one_of_diagonalShape (m : ℕ) (l : Model m)
    (hl : l ∈ fullLevi m) (a b : CoefficientField m)
    (hs : reindex (modelMatrix m l) = diagonalShape a b) : modelMatrix m l = 1 := by
  have ha : a = 1 := by
    have h := congrArg (fun A : Matrix (Fin 52) (Fin 52) (CoefficientField m) => A 0 0) hs
    rw [fullLevi_cartan_entry m l hl] at h
    simpa [diagonalShape, exceptional] using h.symm
  subst a
  have hd : (reindex (modelMatrix m l)).det = 1 := by
    change ((modelMatrix m l).submatrix basisEquiv basisEquiv).det = 1
    rw [Matrix.det_submatrix_equiv_self]
    exact splitGroup_det m (toSplitGroup m l)
  rw [hs, diagonalShape_one_det] at hd
  have hb := coefficient_cube_eq_one m b hd
  subst b
  apply reindex.injective
  simpa [diagonalShape] using hs

lemma fullLevi_eq_one_of_diagonalShape (m : ℕ) (l : Model m)
    (hl : l ∈ fullLevi m) (a b : CoefficientField m)
    (hs : reindex (modelMatrix m l) = diagonalShape a b) : l = 1 := by
  apply toSplitGroup_injective m
  apply Subtype.ext
  apply Units.ext
  change modelMatrix m l = modelMatrix m 1
  rw [modelMatrix_one]
  exact modelMatrix_eq_one_of_diagonalShape m l hl a b hs

end ReeF4.SectionGeometry.LinearRadical.LeviDetection.RootCentralizer
