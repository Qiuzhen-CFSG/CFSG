module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Reduction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.Quartic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.Columns
/-!
# Detecting the quadratic coefficient on Cartan columns

For a second root endpoint, root-string saturation gives the intermediate
root. The actual vector-action formulas identify `R_r v_i` with `E v_r` in
characteristic two. Hence `E R_r E` kills Cartan columns because `E² = 0`.
The remaining term is the second divided-power column multiplied by the
root-coroot pairing. Endpoint and starting-root pairings agree modulo two,
and a nonzero simple-coroot pairing detects the scalar in the endpoint line.

Sources: the actual routed vector actions in `IntegralChevalleyBrackets`,
the divided powers in `IntegralGeckConstruction`, and the F4 Cartan detector
proved in `RootSums.Columns`.
-/

public section
open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
set_option maxHeartbeats 800000

private lemma quadratic_first_root (i : typeF4RootPairing_base.support) (r k : typeF4Roots)
    (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    ∃ s : typeF4Roots,
      typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r := by
  let := typeF4RootPairing.indexNeg
  have hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root r] := by
    refine RootPairing.IsReduced.linearIndependent typeF4RootPairing hpos.symm ?_
    intro h
    apply hneg
    apply typeF4RootPairing.root.injective
    rw [show typeF4RootPairing.root (-i : typeF4Roots) = -typeF4RootPairing.root i by
      simp only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
        typeF4RootPairing.reflection_apply_self]]
    exact ((neg_eq_iff_eq_neg).2 h).symm
  have htwo := (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp ⟨k, hk⟩
  obtain ⟨s, hs⟩ := (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mpr
    (show 1 ≤ typeF4RootPairing.chainTopCoeff i r by omega)
  exact ⟨s, by simpa only [one_smul, add_comm] using hs⟩

private lemma quadratic_pairing (m : ℕ) (i j : typeF4RootPairing_base.support)
    (r k : typeF4Roots)
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    (typeF4RootPairing.pairingIn ℤ k j : CoefficientField m) =
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) := by
  have hp : typeF4RootPairing.pairingIn ℤ k j =
      typeF4RootPairing.pairingIn ℤ r j + 2 * typeF4RootPairing.pairingIn ℤ i j := by
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    simp only [map_add, map_mul, map_ofNat, RootPairing.algebraMap_pairingIn]
    change typeF4RootPairing.coroot' j (typeF4RootPairing.root k) = _
    rw [hk, map_add, map_nsmul]
    simp only [RootPairing.root_coroot'_eq_pairing, two_smul, two_mul]
  simp only [hp, Int.cast_add, Int.cast_mul, Int.cast_ofNat, CharTwo.two_eq_zero,
    zero_mul, add_zero]

/-- Cartan columns of the quadratic operator agree with those of the second
root column in characteristic two. -/
lemma integralQuadraticComparison_map_cartan (m : ℕ) (i j : typeF4RootPairing_base.support)
    (r k : typeF4Roots)
    (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) *ᵥ
        Pi.single (Sum.inl j) 1 =
      (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m)) *ᵥ
        Pi.single (Sum.inl j) 1 := by
  classical
  let E := dividedPower m i 1
  let B := dividedPower m i 2
  let R := coordinateOperator m (Sum.inr r)
  have hEE : E * E = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change _ = (2 : CoefficientField m) • dividedPower m i 2 at h
    simpa only [CharTwo.two_eq_zero, zero_smul] using h
  obtain ⟨s, hs⟩ := quadratic_first_root i r k hpos hneg hk
  have hRE : R *ᵥ Pi.single (Sum.inr i) 1 = E *ᵥ Pi.single (Sum.inr r) 1 := by
    dsimp only [R, E]
    rw [dividedPower_one_eq_coordinateOperator,
      coordinateOperator_mulVec_root_add m r i s (hs.trans (add_comm _ _)),
      coordinateOperator_mulVec_root_add m i r s hs,
      chainBotCoeff_comm_of_root_add r i s (hs.trans (add_comm _ _))]
  have hmiddle : (E * R * E) *ᵥ Pi.single (Sum.inl j) 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, show E = coordinateOperator m (Sum.inr i) from
      dividedPower_one_eq_coordinateOperator m i, coordinateOperator_mulVec_cartan]
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hRE,
      ← dividedPower_one_eq_coordinateOperator m i]
    change (typeF4RootPairing.pairingIn ℤ i j : CoefficientField m) •
      (E *ᵥ (E *ᵥ Pi.single (Sum.inr r) 1)) = 0
    rw [Matrix.mulVec_mulVec, hEE, Matrix.zero_mulVec, smul_zero]
  rw [map_integralQuadraticOperator, Matrix.add_mulVec, Matrix.sub_mulVec, hmiddle,
    sub_zero, ← Matrix.mulVec_mulVec, coordinateOperator_mulVec_cartan,
    Matrix.mulVec_smul, Matrix.mulVec_single_one]
  change _ • (fun x => dividedPower m i 2 x (Sum.inr r)) +
    (coordinateOperator m (Sum.inr r) * dividedPower m i 2) *ᵥ _ = _
  rw [dividedPower_two_rootColumn m i r k hk, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_single_one]
  change _ + coordinateOperator m (Sum.inr r) *ᵥ
    (fun x => dividedPower m i 2 x (Sum.inl j)) = _
  rw [dividedPower_two_cartanColumn, Matrix.mulVec_zero, add_zero,
    integralQuadraticColumn_of_root i r k hk,
    Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul (CoefficientField m)]
  simp only [Matrix.smul_mulVec, Int.cast_natCast]
  change _ = (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : CoefficientField m) •
    (coordinateOperator m (Sum.inr k) *ᵥ Pi.single (Sum.inl j) 1)
  rw [coordinateOperator_mulVec_cartan, quadratic_pairing m i j r k hk, smul_comm]

/-- Membership in the endpoint root line suffices to identify the quadratic
operator after characteristic-two specialization. -/
lemma integralQuadraticComparison_map_of_mem_root_line (m : ℕ) (i : typeF4RootPairing_base.support)
    (r k : typeF4Roots)
    (hpos : r ≠ (i : typeF4Roots))
    (hneg : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i)
    (hline : ∃ c : CoefficientField m,
      (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
        c • coordinateOperator m (Sum.inr k)) :
    (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
      (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m)) := by
  obtain ⟨c, hc⟩ := hline
  obtain ⟨j, hj⟩ := exists_pairingIn_cast_ne_zero m k
  have hu := integralQuadraticComparison_map_cartan m i j r k hpos hneg hk
  have hcol : (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m)) =
      (((typeF4RootPairing.chainBotCoeff i r + 2).choose 2 : ℕ) : CoefficientField m) •
        coordinateOperator m (Sum.inr k) := by
    rw [integralQuadraticColumn_of_root i r k hk,
      Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul (CoefficientField m)]
    rfl
  rw [hc, hcol] at hu ⊢
  simp only [Matrix.smul_mulVec, coordinateOperator_mulVec_cartan] at hu
  have hv := congrFun hu (Sum.inr k)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hv
  rw [mul_right_cancel₀ hj hv]
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
