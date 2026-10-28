module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation
/-!
# Reading the opposite linear parameters from a braid relation

The root spaces of alpha_1 and alpha_0 + alpha_1 form a two-dimensional
space. The root curves at node 0 act there by upper and lower transvections;
both curves at node 3 fix it. Thus the literal type VI words have the same
restrictions. Reading one coordinate of their length-three braid relation
shows that its two nonzero parameters multiply to one.

The columns are derived from integral root-string formulas and specialized
to the coefficient field. This does not assume an SL2 identification of the
ambient Levi subgroup.

Source: GLS3, Table 2.4 type VI and §§2.4–2.5,
`refs/KGroup/GLS3/chapter2.tex`, and the integral Geck root-string formulas.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup ReeF4.WordRelations
open PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
open scoped Matrix
private local instance linearRigidityBraidIndexNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local notation "s" => typeF4RootPairing_baseEquiv
variable {m : ℕ}
private def V (r : F4Chevalley.Root) : F4Chevalley.BasisIndex → CoefficientField m :=
  Pi.single (.inr r) 1

private theorem cast_column_eq (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ)
    (r q : F4Chevalley.Root) (h : A *ᵥ v (b := typeF4RootPairing_base) r = v (b := typeF4RootPairing_base) q) :
    A.map (Int.castRingHom (CoefficientField m)) *ᵥ V r = V q := by
  classical
  ext k
  have hk := congrArg (Int.castRingHom (CoefficientField m)) (congrFun h k)
  simpa [Matrix.mulVec_single, v, V, Pi.single_apply] using hk

private theorem cast_column_zero (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ)
    (r : F4Chevalley.Root) (h : A *ᵥ v (b := typeF4RootPairing_base) r = 0) :
    A.map (Int.castRingHom (CoefficientField m)) *ᵥ V r = 0 := by
  ext k
  have hk := congrArg (Int.castRingHom (CoefficientField m)) (congrFun h k)
  simpa [Matrix.mulVec_single, v, V] using hk

private theorem simple_not_neg (i j : typeF4RootPairing_base.support) : j.val ≠ -i.val := by
  intro h
  have hp := typeF4RootPairing_base.isPos_of_mem_support j.property
  rw [h, RootPairing.Base.IsPos.neg_iff_not] at hp
  exact hp (typeF4RootPairing_base.isPos_of_mem_support i.property)

private theorem top_one (i j : typeF4RootPairing_base.support) (hne : i ≠ j)
    (h : typeF4RootPairing_base.cartanMatrix j i = -1) : typeF4RootPairing.chainTopCoeff i j = 1 := by
  have he := RootPairing.Base.chainTopCoeff_eq_of_ne (b := typeF4RootPairing_base) hne
  change (typeF4RootPairing.chainTopCoeff i j : ℤ) = -typeF4RootPairing_base.cartanMatrix j i at he
  omega

private theorem positive_simple_column (i j : typeF4RootPairing_base.support) (hne : i ≠ j)
    (hc : typeF4RootPairing_base.cartanMatrix j i = -1) (t : CoefficientField m) :
    positiveMatrix i t *ᵥ V j.val = V j.val + t • V (typeF4RootPairing.reflectionPerm i.val j.val) := by
  have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i.val j.val) = typeF4RootPairing.root i.val + typeF4RootPairing.root j.val := by
    rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root' ℤ]
    change typeF4RootPairing.root j.val - typeF4RootPairing_base.cartanMatrix j i • typeF4RootPairing.root i.val = _
    rw [hc, neg_one_smul, sub_neg_eq_add, add_comm]
  have hE : (eMatrix i).map (Int.castRingHom (CoefficientField m)) *ᵥ V j.val =
      V (typeF4RootPairing.reflectionPerm i.val j.val) := by
    apply cast_column_eq
    simpa only [RootPairing.Base.chainBotCoeff_eq_zero, Nat.cast_zero, zero_add, one_smul] using
      eMatrix_mulVec_v_add (i := i) hr
  have hn (n : ℕ) : (eDividedPower i (n + 2)).map (Int.castRingHom (CoefficientField m)) *ᵥ
      V j.val = 0 := by
    apply cast_column_zero
    apply eDividedPower_add_two_mulVec_v_zero
    rw [typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff (typeF4RootPairing_base.linearIndependent_pair_of_ne hne),
      top_one i j hne hc]
    omega
  rw [positiveMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, eDividedPower_one, hE, hn 0, hn 1,
    smul_zero, add_zero]

private theorem negative_simple_column (i j : typeF4RootPairing_base.support) (hne : i ≠ j)
    (t : CoefficientField m) : negativeMatrix i t *ᵥ V j.val = V j.val := by
  have hF : (fMatrix i).map (Int.castRingHom (CoefficientField m)) *ᵥ V j.val = 0 := by
    apply cast_column_zero
    exact fMatrix_mulVec_v_zero (by exact Subtype.coe_ne_coe.mpr hne.symm)
      (typeF4RootPairing_base.sub_notMem_range_root j.property i.property)
  have hn (n : ℕ) : (fDividedPower i (n + 2)).map (Int.castRingHom (CoefficientField m)) *ᵥ
      V j.val = 0 := by
    apply cast_column_zero
    apply fDividedPower_add_two_mulVec_v_zero
    rw [typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff (typeF4RootPairing_base.linearIndependent_pair_of_ne hne),
      RootPairing.Base.chainBotCoeff_eq_zero]
    omega
  rw [negativeMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, fDividedPower_one, hF, hn 0, hn 1,
    smul_zero, add_zero]

private theorem positive_simple_column_zero (i j : typeF4RootPairing_base.support) (hne : i ≠ j)
    (hc : typeF4RootPairing_base.cartanMatrix j i = 0) (t : CoefficientField m) :
    positiveMatrix i t *ᵥ V j.val = V j.val := by
  have htop : typeF4RootPairing.chainTopCoeff i j = 0 := by
    have he := RootPairing.Base.chainTopCoeff_eq_of_ne (b := typeF4RootPairing_base) hne
    change (typeF4RootPairing.chainTopCoeff i j : ℤ) = -typeF4RootPairing_base.cartanMatrix j i at he
    omega
  have hnot (n : ℕ) (hn : n ≠ 0) : typeF4RootPairing.root j.val + n • typeF4RootPairing.root i.val ∉ Set.range typeF4RootPairing.root := by
    rw [typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff (typeF4RootPairing_base.linearIndependent_pair_of_ne hne), htop]
    omega
  have hE : (eMatrix i).map (Int.castRingHom (CoefficientField m)) *ᵥ V j.val = 0 := by
    apply cast_column_zero
    exact eMatrix_mulVec_v_zero (simple_not_neg i j) (by simpa [add_comm] using hnot 1 (by decide))
  have hn (n : ℕ) : (eDividedPower i (n + 2)).map (Int.castRingHom (CoefficientField m)) *ᵥ
      V j.val = 0 := by
    apply cast_column_zero
    exact eDividedPower_add_two_mulVec_v_zero i j n (hnot (n+2) (by omega))
  rw [positiveMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, eDividedPower_one, hE, hn 0, hn 1,
    smul_zero, add_zero]

private theorem tits_column (i : typeF4RootPairing_base.support) (r : F4Chevalley.Root) :
    (titsUnit (S := CoefficientField m) [i]).val *ᵥ V r = V (typeF4RootPairing.reflectionPerm i.val r) := by
  classical
  ext k
  have h := congrFun (titsLift_mulVec_v i r) k
  have hc : titsLift i k (.inr r) =
      if k = .inr (typeF4RootPairing.reflectionPerm i r) then (-1 : ℤ) ^ typeF4RootPairing.chainBotCoeff i r else 0 := by
    simpa [v, Pi.single_apply] using h
  change (specializeMatrix (titsLift i * 1) *ᵥ V r) k = _
  simp only [mul_one, V, Matrix.mulVec_single_one]
  change (titsLift i k (.inr r) : CoefficientField m) = _
  rw [hc]
  split_ifs <;> simp_all [CharTwo.neg_eq]

private def pX (i : Fin 4) (t : CoefficientField m) :=
  F4Chevalley.rootCurve (typeF4SimpleRootIndex i) t
private def pY (i : Fin 4) (t : CoefficientField m) :=
  F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) t
private def pW (m : ℕ) : MatrixUnits m := titsUnit [s 0]
private def E₀ : F4Chevalley.BasisIndex → CoefficientField m := V (typeF4SimpleRootIndex 1)
private def E₁ : F4Chevalley.BasisIndex → CoefficientField m :=
  V (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 1))

private theorem pX_val (i : Fin 4) (t : CoefficientField m) :
    (pX i t).val = positiveMatrix (s i) t := by
  simp only [pX, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, positiveUnit_val]
private theorem pY_val (i : Fin 4) (t : CoefficientField m) :
    (pY i t).val = negativeMatrix (s i) t := by
  simp only [pY, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_neg_simple, negativeUnit_val]
private theorem pW_inv : (pW m)⁻¹ = pW m := by
  simp only [pW, titsUnit_cons, titsUnit_nil, mul_one, mul_inv_rev,
    F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  group
private theorem pW_E₀ : (pW m).val *ᵥ E₀ = E₁ := tits_column (s 0) _
private theorem pW_E₁ : (pW m).val *ᵥ E₁ = E₀ := by
  change (titsUnit (S := CoefficientField m) [s 0]).val *ᵥ V _ = _
  rw [tits_column]
  simp only [typeF4RootPairing_baseEquiv_val, RootPairing.reflectionPerm_self, E₀]

private theorem pX_E₀ (t : CoefficientField m) :
    (pX 0 t).val *ᵥ E₀ = E₀ + t • E₁ := by
  rw [pX_val]
  exact positive_simple_column (s 0) (s 1)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (by rw [typeF4RootPairing_base_cartan_apply]; rfl) t
private theorem pY_E₀ (t : CoefficientField m) :
    (pY 0 t).val *ᵥ E₀ = E₀ := by
  rw [pY_val]
  exact negative_simple_column (s 0) (s 1)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction) t
private theorem pW_pX (t : CoefficientField m) :
    pW m * pX 0 t * (pW m)⁻¹ = pY 0 t := simple_conj (s 0) _ t
private theorem pW_pY (t : CoefficientField m) :
    pW m * pY 0 t * (pW m)⁻¹ = pX 0 t := by
  change titsUnit [s 0] * F4Chevalley.rootCurve _ t * (titsUnit [s 0])⁻¹ = _
  rw [simple_conj]
  change F4Chevalley.rootCurve
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 0))) t = _
  rw [RootPairing.reflectionPerm_self]
  rfl
private theorem pX_E₁ (t : CoefficientField m) :
    (pX 0 t).val *ᵥ E₁ = E₁ := by
  rw [← pW_pY, pW_inv, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pW_E₁, pY_E₀, pW_E₀]
private theorem pY_E₁ (t : CoefficientField m) :
    (pY 0 t).val *ᵥ E₁ = E₁ + t • E₀ := by
  rw [← pW_pX, pW_inv, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pW_E₁, pX_E₀,
    Matrix.mulVec_add, Matrix.mulVec_smul, pW_E₀, pW_E₁]
private theorem pX_three_E₀ (t : CoefficientField m) :
    (pX 3 t).val *ᵥ E₀ = E₀ := by
  rw [pX_val]
  exact positive_simple_column_zero (s 3) (s 1)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (by rw [typeF4RootPairing_base_cartan_apply]; rfl) t
private theorem pY_three_E₀ (t : CoefficientField m) :
    (pY 3 t).val *ᵥ E₀ = E₀ := by
  rw [pY_val]
  exact negative_simple_column (s 3) (s 1)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction) t

private theorem fixes_second (B : MatrixUnits m)
    (hB : B.val *ᵥ E₀ = E₀) (hc : Commute (pX 0 (1 : CoefficientField m)) B) :
    B.val *ᵥ E₁ = E₁ := by
  have h := congrArg (fun A : MatrixUnits m => A.val *ᵥ E₀) hc.eq
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, pX_E₀, one_smul,
    Matrix.mulVec_add, hB] at h
  exact (add_left_cancel h).symm
private theorem pX_three_E₁ (t : CoefficientField m) :
    (pX 3 t).val *ᵥ E₁ = E₁ := by
  apply fixes_second _ (pX_three_E₀ t)
  have h := commute_positive_positive_of_cartan_eq_zero (s 0) (s 3)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (by rw [typeF4RootPairing_base_cartan_apply]; rfl) (1 : CoefficientField m) t
  apply Units.ext
  simpa only [Subgroup.coe_mul, positive, negative, Units.val_mul, positiveUnit_val, pX_val] using
    congrArg (fun A => A.val.val) h.eq
private theorem pY_three_E₁ (t : CoefficientField m) :
    (pY 3 t).val *ᵥ E₁ = E₁ := by
  apply fixes_second _ (pY_three_E₀ t)
  have h := commute_positive_negative (s 0) (s 3)
    (by intro h; have := typeF4RootPairing_baseEquiv.injective h; contradiction)
    (1 : CoefficientField m) t
  apply Units.ext
  simpa only [Subgroup.coe_mul, positive, negative, Units.val_mul, positiveUnit_val, negativeUnit_val, pX_val, pY_val] using
    congrArg (fun A => A.val.val) h.eq

private theorem linear_true_E₀ (t : CoefficientField m) :
    (linearWord m true t).val.val *ᵥ E₀ = E₀ + t • E₁ := by
  change (pX 0 t * pX 3 (theta m t)).val *ᵥ E₀ = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, pX_three_E₀, pX_E₀]
private theorem linear_true_E₁ (t : CoefficientField m) :
    (linearWord m true t).val.val *ᵥ E₁ = E₁ := by
  change (pX 0 t * pX 3 (theta m t)).val *ᵥ E₁ = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, pX_three_E₁, pX_E₁]
private theorem linear_false_E₀ (t : CoefficientField m) :
    (linearWord m false t).val.val *ᵥ E₀ = E₀ := by
  change (pY 0 t * pY 3 (theta m t)).val *ᵥ E₀ = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, pY_three_E₀, pY_E₀]
private theorem linear_false_E₁ (t : CoefficientField m) :
    (linearWord m false t).val.val *ᵥ E₁ = E₁ + t • E₀ := by
  change (pY 0 t * pY 3 (theta m t)).val *ᵥ E₁ = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, pY_three_E₁, pY_E₁]

/-- The opposite type VI braid determines its two nonzero parameters. -/
theorem linearElement_braid_parameter (d : LocalBlockInput m)
    (t u : CoefficientField m) (ht : t ≠ 0)
    (h : linearElement d true t * linearElement d false u * linearElement d true t =
      linearElement d false u * linearElement d true t * linearElement d false u) :
    t * u = 1 := by
  have he := congrArg (fun x : d.fixedGroup => x.val.val.val *ᵥ E₀) h
  simp only [Subgroup.coe_mul, Units.val_mul, linearElement_word, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul,
    linear_true_E₀, linear_true_E₁, linear_false_E₀, linear_false_E₁] at he
  let r := typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 1)
  have hcoord := congrFun he (.inr r)
  have hscalar : t * (t * u) = t * 1 := by
    simp only [E₀, E₁, V, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Sum.inr.injEq, show r = typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 1) from rfl, ↓reduceIte, mul_one] at hcoord
    linear_combination hcoord - CharTwo.add_self_eq_zero t
  exact mul_left_cancel₀ ht hscalar

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

end
