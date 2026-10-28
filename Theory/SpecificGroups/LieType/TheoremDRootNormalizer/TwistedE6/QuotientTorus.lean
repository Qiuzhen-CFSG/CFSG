module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Coordinates
public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.TwistedE6.Quotient
import Mathlib.Tactic

/-!
# A faithful torus in the genuine twisted E6 root normalizer

Assume a homomorphism lifting the published four-coordinate diagonal torus
into the defining-characteristic subgroup, with its literal matrix formula.
The fourth coroot then detects every nonidentity element of the full fixed
root curve at node 3, so that curve survives the quotient by the subgroup's
own center. The first three folded root characters detect every element of
the three-coordinate torus in the same quotient. Their conjugation formulas
place the resulting faithful torus in the actual root normalizer.

For the paired positive curves, an ordinary ambient simple-coroot diagonal
separates the orthogonal factors, and a distinguished matrix entry recovers
the parameter. This ambient calculation establishes only parameter
faithfulness. Every use of quotient centrality tests actual elements of the
defining-characteristic subgroup, including the supplied torus lift.

These are geometric inputs to the torus obstruction of Aschbacher–Smith
A.2.18, printed p.40. Root, residual and center-quotient conventions follow
GLS3 §§2.2–2.4, especially 2.2.6 and Table 2.4
(`refs/KGroup/GLS3/chapter2.tex`). Construction of the lift remains a separate
premise; no recognition of an auxiliary folded carrier is used.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.TheoremDRootNormalizer
noncomputable section
attribute [local instance] Classical.decEq

private theorem fixed_unit_square (m : ℕ) (hm : 0 < m) :
    ∃ u : (FixedField m)ˣ, (u : FixedField m) ^ 2 ≠ 1 := by
  have hc : 1 < Nat.card (FixedField m)ˣ := by
    rw [Nat.card_units]
    have := fixedField_card_gt_two m hm
    omega
  let : Nontrivial (FixedField m)ˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨u, hu⟩ := exists_ne (1 : (FixedField m)ˣ)
  refine ⟨u, fun h => hu (Units.ext ?_)⟩
  apply frobenius_inj (FixedField m) 2
  change (u : FixedField m) ^ 2 = (1 : FixedField m) ^ 2
  simpa only [one_pow] using h

private theorem positive_injective (m : ℕ) (i : Fin 6) :
    Function.Injective (fun x => (splitSimple m true i x).val) := by
  let := Pairing.indexNeg
  intro x y h
  have he := congrArg (fun g : AmbientGroup 2 m =>
    g.val (Sum.inl (simpleIndex i)) (Sum.inr (-(simpleIndex i) : typeE6Roots))) h
  change (rootCurveUnit (integralChevalleyRootOperators (P := Pairing) (b := Base))
      (simpleIndex i) x).val _ _ =
    (rootCurveUnit (integralChevalleyRootOperators (P := Pairing) (b := Base))
      (simpleIndex i) y).val _ _ at he
  simpa only [ExceptionalSplit.TheoremDRootNormalizer.simpleRoot_entry] using he

private theorem positive_conjugation (m : ℕ)
    (a : Base.support → (CoefficientField 2 m)ˣ) (i : Fin 6) (x : CoefficientField 2 m) :
    (integralChevalleyTorusElement (P := Pairing) a)⁻¹ *
      (splitSimple m true i x).val * integralChevalleyTorusElement (P := Pairing) a =
    (splitSimple m true i ((integralChevalleyRootScale (P := Pairing) a (simpleIndex i) :
      CoefficientField 2 m) * x)).val := by
  exact integralChevalleyRootCurve_torus_conjugation a (simpleIndex i) x

-- Only ambient equality is used here; the separating diagonal need not be fixed.
private theorem pair_kernel (m : ℕ) (hm : 0 < m) (i j : Fin 6)
    (hc : typeE6CartanMatrix j i = 0) (x : CoefficientField 2 m)
    (hx : (splitSimple m true i x).val * (splitSimple m true j x).val = 1) : x = 0 := by
  obtain ⟨u, hu⟩ := fixed_unit_square m hm
  let v := coefficientUnit m u
  have hv : (v : CoefficientField 2 m) ^ 2 ≠ 1 := by
    intro h
    apply hu
    exact Subtype.val_injective (by simpa [v] using h)
  let a := integralChevalleySimpleCorootParameter (simpleIndex i) v
  let d := integralChevalleyTorusElement (P := Pairing) a
  have hscale : integralChevalleyRootScale (P := Pairing) a (simpleIndex j) = 1 := by
    have hp : Pairing.pairingIn ℤ (simpleIndex j) (simpleIndex i) =
        typeE6CartanMatrix j i := typeE6RootPairing_base_cartan_apply j i
    dsimp only [a]
    rw [integralChevalleyRootScale_simpleCorootParameter, hp, hc, zpow_zero]
  have hscale_self : integralChevalleyRootScale (P := Pairing) a (simpleIndex i) = v ^ 2 := by
    simp [a]
  have he : (splitSimple m true i ((v : CoefficientField 2 m) ^ 2 * x)).val *
      (splitSimple m true j x).val = 1 := by
    calc
      _ = (d⁻¹ * (splitSimple m true i x).val * d) *
          (d⁻¹ * (splitSimple m true j x).val * d) := by
        simp only [d, positive_conjugation, hscale, hscale_self, Units.val_pow_eq_pow_val,
          Units.val_one, one_mul]
      _ = d⁻¹ * ((splitSimple m true i x).val * (splitSimple m true j x).val) * d := by group
      _ = 1 := by rw [hx]; group
  have hf := positive_injective m i (mul_right_cancel (he.trans hx.symm))
  have hz : ((v : CoefficientField 2 m) ^ 2 - 1) * x = 0 := by
    simpa [sub_mul] using sub_eq_zero.mpr hf
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hv)

/-- Faithfulness on all fixed parameters, including the two paired curves. -/
theorem foldedRoot_positive_injective (m : ℕ) (hm : 0 < m) (i : Fin 4) :
    Function.Injective (foldedRoot m true i) := by
  have hi : Function.Injective (foldedRootHom m true i) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have he := congrArg (ambientInclusion m) hx
    change (foldedSplit m true i x.toAdd).val = 1 at he
    have hz : x.toAdd = 0 := by
      apply Subtype.val_injective
      fin_cases i
      · exact pair_kernel m hm 0 5 (by decide) x.toAdd he
      · exact pair_kernel m hm 1 4 (by decide) x.toAdd he
      · exact positive_injective m 2 (he.trans (by simp))
      · exact positive_injective m 3 (he.trans (by simp))
    exact congrArg Multiplicative.ofAdd hz
  intro x y h
  exact congrArg Multiplicative.toAdd (hi h)

private theorem folded_matrix_conjugation (m : ℕ) (a : Fin 4 → (FixedField m)ˣ)
    (i : Fin 4) (x : FixedField m) :
    (foldedTorusMatrix m a)⁻¹ * (foldedSplit m true i x).val * foldedTorusMatrix m a =
      (foldedSplit m true i ((foldedCharacter a i : FixedField m) * x)).val := by
  have hp (j : Fin 6) :
      (foldedTorusMatrix m a)⁻¹ * (splitSimple m true j x).val * foldedTorusMatrix m a =
        (splitSimple m true j (((foldedCharacter a (orbitIndex j) : FixedField m) * x :
          FixedField m) : CoefficientField 2 m)).val := by
    change (integralChevalleyTorusElement (P := Pairing) (foldedParameters m a))⁻¹ *
      (splitSimple m true j x).val * integralChevalleyTorusElement (P := Pairing) _ = _
    rw [positive_conjugation, foldedParameters_scale]
    rfl
  have hpairs (j k : Fin 6) :
      (foldedTorusMatrix m a)⁻¹ *
        ((splitSimple m true j x).val * (splitSimple m true k x).val) * foldedTorusMatrix m a =
      (splitSimple m true j (((foldedCharacter a (orbitIndex j) : FixedField m) * x :
          FixedField m) : CoefficientField 2 m)).val *
        (splitSimple m true k (((foldedCharacter a (orbitIndex k) : FixedField m) * x :
          FixedField m) : CoefficientField 2 m)).val := by
    rw [← hp j, ← hp k]
    group
  fin_cases i
  · exact hpairs 0 5
  · exact hpairs 1 4
  · exact hp 2
  · exact hp 3

variable (m : ℕ) (t : (Fin 4 → (FixedField m)ˣ) →* definingCharacteristicSubgroup 2 m)
  (ht : ∀ a, ambientInclusion m (t a) = foldedTorusMatrix m a)

include ht

/-- The root character acts inside the actual defining-characteristic subgroup. -/
theorem liftedTorus_conjugation (a : Fin 4 → (FixedField m)ˣ) (i : Fin 4) (x : FixedField m) :
    (t a)⁻¹ * foldedRoot m true i x * t a =
      foldedRoot m true i ((foldedCharacter a i : FixedField m) * x) := by
  apply ambientInclusion_injective m
  simp only [map_mul, map_inv, ht, foldedRoot_ambient]
  exact folded_matrix_conjugation m a i x

/-- The full fixed curve at node 3 survives the literal center quotient. -/
theorem projectiveRootHom_injective_of_torus_lift (hm : 0 < m) :
    Function.Injective (projectiveRootHom m true 3) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : foldedRoot m true 3 x.toAdd ∈ Subgroup.center (definingCharacteristicSubgroup 2 m) :=
    (toModel_eq_one 2 m _).mp hx
  obtain ⟨u, hu⟩ := fixed_unit_square m hm
  let a : Fin 4 → (FixedField m)ˣ := ![1, 1, 1, u]
  have hcomm := Subgroup.mem_center_iff.mp hc (t a)
  have he : (t a)⁻¹ * foldedRoot m true 3 x.toAdd * t a = foldedRoot m true 3 x.toAdd := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  rw [liftedTorus_conjugation m t ht] at he
  have hf := foldedRoot_positive_injective m hm 3 he
  have hz : ((u : FixedField m) ^ 2 - 1) * x.toAdd = 0 := by
    simpa [a, foldedCharacter, sub_mul] using sub_eq_zero.mpr hf
  exact congrArg Multiplicative.ofAdd ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hu))

/-- Relative centrality forces trivial characters on actual folded positive curves. -/
theorem foldedCharacter_eq_one_of_projective_lift_eq_one (hm : 0 < m)
    (a : Fin 4 → (FixedField m)ˣ) (ha : toModel 2 m (t a) = 1) (i : Fin 4) :
    foldedCharacter a i = 1 := by
  have hc := (toModel_eq_one 2 m _).mp ha
  have hcomm := Subgroup.mem_center_iff.mp hc (foldedRoot m true i 1)
  have he : (t a)⁻¹ * foldedRoot m true i 1 * t a = foldedRoot m true i 1 := by
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  rw [liftedTorus_conjugation m t ht, mul_one] at he
  exact Units.ext (foldedRoot_positive_injective m hm i he)

theorem liftedTorus_projective_conjugation (a : Fin 4 → (FixedField m)ˣ)
    (i : Fin 4) (x : FixedField m) :
    (toModel 2 m (t a))⁻¹ * projectiveRootHom m true i (Multiplicative.ofAdd x) *
      toModel 2 m (t a) =
    projectiveRootHom m true i (Multiplicative.ofAdd ((foldedCharacter a i : FixedField m) * x)) := by
  change (toModel 2 m (t a))⁻¹ * toModel 2 m (foldedRoot m true i x) *
    toModel 2 m (t a) = toModel 2 m (foldedRoot m true i ((foldedCharacter a i : FixedField m) * x))
  simpa only [map_mul, map_inv] using
    congrArg (toModel 2 m) (liftedTorus_conjugation m t ht a i x)

theorem liftedTorus_mem_rootNormalizer (a : Fin 4 → (FixedField m)ˣ) :
    toModel 2 m (t a) ∈ rootNormalizer m := by
  have hf (a : Fin 4 → (FixedField m)ˣ) (g : Model 2 m) (hg : g ∈ rootSubgroup m) :
      (toModel 2 m (t a))⁻¹ * g * toModel 2 m (t a) ∈ rootSubgroup m := by
    obtain ⟨x, rfl⟩ := hg
    change (toModel 2 m (t a))⁻¹ * projectiveRootHom m true 3 (Multiplicative.ofAdd x.toAdd) *
      toModel 2 m (t a) ∈ _
    rw [liftedTorus_projective_conjugation m t ht]
    exact ⟨_, rfl⟩
  rw [rootNormalizer, Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    simpa only [map_inv, inv_inv] using hf a⁻¹ g hg
  · intro hg
    simpa only [inv_mul_cancel_left, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one] using hf a _ hg

/-- The three-coordinate lifted torus, in the normalizer of the full fixed root curve. -/
def liftedTorusNormalizer : (Fin 3 → (FixedField m)ˣ) →* rootNormalizer m :=
  (((toModel 2 m).comp t).comp (threeCoordinates m)).codRestrict _
    (fun a => liftedTorus_mem_rootNormalizer m t ht (threeCoordinates m a))

@[simp] theorem liftedTorusNormalizer_val (a : Fin 3 → (FixedField m)ˣ) :
    (liftedTorusNormalizer m t ht a).val = toModel 2 m (t (threeCoordinates m a)) := rfl

/-- Three folded characters detect the torus after quotienting by the residual's center. -/
theorem liftedTorusNormalizer_injective (hm : 0 < m) :
    Function.Injective (liftedTorusNormalizer m t ht) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have he : toModel 2 m (t (threeCoordinates m a)) = 1 := congrArg Subtype.val ha
  apply threeCoordinates_injective m
  rw [map_one]
  apply foldedCharacter_separate m _ (threeCoordinates_last m a)
  intro i
  exact foldedCharacter_eq_one_of_projective_lift_eq_one m t ht hm _ he i.castSucc

end
end TwistedE6.TheoremDRootNormalizer
