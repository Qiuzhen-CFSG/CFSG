module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RouteOperators
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets


/-!
# Cartan-column detection of the F4 root commutator

In characteristic two every routed root operator sends a simple Cartan vector
`u_j` to the Cartan pairing times its root vector. Weyl covariance of the actual
operators proves this formula along any positive-source route. Each root has a
Cartan pairing nonzero in characteristic two: this holds on the displayed F4
base, and the reflection formula preserves the assertion.

The all-root vector-action formula and the absence of three-step F4 strings
then show that the root-sum commutator has the required Cartan columns. These
columns determine its coefficient once it is known to lie in the sum-root
operator line. The operator-line premise is discharged in `RootSums.RootSpace`.

Sources: Geck's integral construction in `IntegralGeckConstruction`, the
vector-action theorem in `IntegralChevalleyBrackets`, and the F4 root-length
bound in `Intertwining.Simple.RootGeometry`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

private lemma cast_mulVec (m : ℕ) (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom (CoefficientField m)) ∘ (A *ᵥ v) =
      A.map (Int.castRingHom (CoefficientField m)) *ᵥ
        ((Int.castRingHom (CoefficientField m)) ∘ v) := by
  ext x
  exact (Int.castRingHom (CoefficientField m)).map_mulVec A v x

private lemma cast_single (m : ℕ) (j : Coordinate) :
    (Int.castRingHom (CoefficientField m)) ∘ Pi.single j (1 : ℤ) = Pi.single j 1 := by
  classical
  ext x
  simp [Pi.single_apply]

private lemma cast_smul (m : ℕ) (z : ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom (CoefficientField m)) ∘ (z • v) =
      (z : CoefficientField m) • ((Int.castRingHom (CoefficientField m)) ∘ v) := by
  ext x
  simp

private lemma cast_sign (m : ℕ) (z : ℤ) (hz : z * z = 1) :
    (z : CoefficientField m) = 1 := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hz with h | h <;>
    simp [h, CharTwo.neg_eq]

private lemma cast_rootVector (m : ℕ) (r : typeF4Roots) :
    (Int.castRingHom (CoefficientField m)) ∘
      rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) r =
        Pi.single (Sum.inr r) 1 := by
  obtain ⟨z, hz, hv⟩ := exists_rootVector_sign (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r
  rw [hv, cast_smul, cast_sign m z hz, one_smul, v, cast_single]

/-- Root addition gives the actual operator action on a root basis vector. -/
lemma coordinateOperator_mulVec_root_add (m : ℕ) (r t s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root r + typeF4RootPairing.root t) :
    coordinateOperator m (Sum.inr r) *ᵥ Pi.single (Sum.inr t) 1 =
      (typeF4RootPairing.chainBotCoeff r t + 1 : CoefficientField m) •
        Pi.single (Sum.inr s) 1 := by
  obtain ⟨z, hz, hv⟩ := rootOperator_mulVec_root_add_signed
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) h
  have hc := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v) hv
  rw [cast_mulVec, cast_smul, cast_rootVector, cast_rootVector] at hc
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
    (Int.castRingHom (CoefficientField m)) *ᵥ _ = _
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    cast_sign m z hz, one_mul] using hc

/-- When the sum is a root, the two F4 lower string lengths agree. -/
lemma chainBotCoeff_comm_of_root_add (r t s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root r + typeF4RootPairing.root t) :
    typeF4RootPairing.chainBotCoeff r t = typeF4RootPairing.chainBotCoeff t r := by
  let P := typeF4RootPairing
  have bound (r t s : typeF4Roots) (h : P.root s = P.root r + P.root t) :
      P.chainBotCoeff r t ≤ 1 := by
    have hlin := P.linearIndependent_of_add_mem_range_root' ⟨s, h⟩
    by_contra hn
    obtain ⟨l, hl⟩ := (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).mpr
      (show 2 ≤ P.chainBotCoeff r t by omega)
    apply root_ne_add_three_nsmul r l s
    rw [h, hl]
    module
  have hrt := bound r t s h
  have htr := bound t r s (h.trans (add_comm _ _))
  have hz : P.chainBotCoeff r t = 0 ↔ P.chainBotCoeff t r = 0 := by
    rw [P.chainBotCoeff_eq_zero_iff, P.chainBotCoeff_eq_zero_iff]
    have hlin := P.linearIndependent_of_add_mem_range_root' ⟨s, h⟩
    have hlin' := P.linearIndependent_of_add_mem_range_root' ⟨s, h.trans (add_comm _ _)⟩
    simp only [hlin, hlin', not_true_eq_false, false_or]
    let := P.indexNeg
    constructor <;> intro hn hm <;> apply hn
    · obtain ⟨k, hk⟩ := hm
      refine ⟨-k, ?_⟩
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self, hk]
      abel
    · obtain ⟨k, hk⟩ := hm
      refine ⟨-k, ?_⟩
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self, hk]
      abel
  omega

private lemma cast_abs (m : ℕ) (a : ℤ) :
    ((|a| : ℤ) : CoefficientField m) = (a : CoefficientField m) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Int.cast_neg, CharTwo.neg_eq]

private lemma pairingIn_reflection (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) (j : typeF4RootPairing_base.support) :
    typeF4RootPairing.pairingIn ℤ (typeF4RootPairing.reflectionPerm i r) j =
      typeF4RootPairing.pairingIn ℤ r j -
        typeF4RootPairing_base.cartanMatrix i j * typeF4RootPairing.pairingIn ℤ r i := by
  have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i r) =
      (1 : ℤ) • typeF4RootPairing.root r +
        (-typeF4RootPairing.pairingIn ℤ r i) • typeF4RootPairing.root i := by
    rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
    simp only [one_smul, neg_smul, ← sub_eq_add_neg]
    rw [← Int.cast_smul_eq_zsmul ℝ, ← typeF4RootPairing.algebraMap_pairingIn ℤ]
    rfl
  have h := RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul
    (P := typeF4RootPairing) (S := ℤ) (j := j.val) hr
  simpa only [one_smul, smul_eq_mul, one_mul, neg_mul, ← sub_eq_add_neg,
    RootPairing.Base.cartanMatrixIn_def, mul_comm] using h

private lemma tits_map_inv (m : ℕ) (i : typeF4RootPairing_base.support) :
    (titsLiftInv (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) =
      (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) := by
  simp only [titsLiftInv, titsLift, Matrix.map_mul, map_eUnipotent, map_fUnipotent,
    Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

private lemma tits_map_root (m : ℕ) (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) *ᵥ
      Pi.single (Sum.inr r) 1 = Pi.single (Sum.inr (typeF4RootPairing.reflectionPerm i r)) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
      (titsLift_mulVec_v (P := typeF4RootPairing) i r)
  simpa only [cast_mulVec, cast_smul, v, cast_single, Int.cast_pow,
    Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_pow, one_smul] using h

private lemma tits_map_cartan (m : ℕ) (i j : typeF4RootPairing_base.support) :
    (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField m)) *ᵥ
      Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 +
        (typeF4RootPairing_base.cartanMatrix i j : CoefficientField m) •
          Pi.single (Sum.inl i) 1 := by
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
      (titsLift_mulVec_u (P := typeF4RootPairing) i j)
  have hsub (v w : Coordinate → ℤ) :
      (Int.castRingHom (CoefficientField m)) ∘ (v - w) =
        (Int.castRingHom (CoefficientField m)) ∘ v -
          (Int.castRingHom (CoefficientField m)) ∘ w := by ext x; simp
  rw [cast_mulVec, hsub, cast_smul, u, u, cast_single, cast_single, cast_abs] at h
  simpa only [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq] using h

private lemma simple_map_cartan (m : ℕ) (i j : typeF4RootPairing_base.support) :
    coordinateOperator m (Sum.inr i.val) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ i j : CoefficientField m) •
        Pi.single (Sum.inr i.val) 1 := by
  rw [← dividedPower_one_eq_coordinateOperator]
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
      (eMatrix_mulVec_u (P := typeF4RootPairing) i j)
  simpa only [cast_mulVec, cast_smul, u, v, cast_single, cast_abs,
    RootPairing.Base.cartanMatrixIn_def, dividedPower, eDividedPower_one] using h

/-- The actual routed root operator acts on Cartan columns by the root pairing. -/
lemma coordinateOperator_mulVec_cartan (m : ℕ) (r : typeF4Roots)
    (j : typeF4RootPairing_base.support) :
    coordinateOperator m (Sum.inr r) *ᵥ Pi.single (Sum.inl j) 1 =
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) •
        Pi.single (Sum.inr r) 1 := by
  have route (w : List typeF4RootPairing_base.support) (k : typeF4RootPairing_base.support) :
      ∀ j : typeF4RootPairing_base.support,
      coordinateOperator m (Sum.inr (reflectionWord (P := typeF4RootPairing) w k)) *ᵥ
        Pi.single (Sum.inl j) 1 =
          (typeF4RootPairing.pairingIn ℤ (reflectionWord (P := typeF4RootPairing) w k) j :
            CoefficientField m) • Pi.single (Sum.inr (reflectionWord (P := typeF4RootPairing) w k)) 1 := by
    induction w with
    | nil => exact simple_map_cartan m k
    | cons i w ih =>
      intro j
      let t := reflectionWord (P := typeF4RootPairing) w k
      have hc := coordinateOperator_reflectionWord m [i] t
      simp only [reflectionWord, titsWord, titsWordInv_cons, titsWordInv_nil,
        mul_one, one_mul] at hc
      change coordinateOperator m (Sum.inr (typeF4RootPairing.reflectionPerm i t)) *ᵥ _ = _
      rw [hc, tits_map_inv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        tits_map_cartan, Matrix.mulVec_add, Matrix.mulVec_smul, ih j, ih i]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, tits_map_root, reflectionWord]
      rw [pairingIn_reflection, Int.cast_sub, Int.cast_mul]
      simp only [sub_eq_add_neg, CharTwo.neg_eq,
        add_smul, mul_smul]
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  simpa only [z.target] using route z.word z.simple j

/-- Every F4 root is detected by a simple coroot in characteristic two. -/
lemma exists_pairingIn_cast_ne_zero (m : ℕ) (r : typeF4Roots) :
    ∃ j : typeF4RootPairing_base.support,
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) ≠ 0 := by
  have simple (i : typeF4RootPairing_base.support) :
      ∃ j : typeF4RootPairing_base.support,
        (typeF4RootPairing.pairingIn ℤ i j : CoefficientField m) ≠ 0 := by
    obtain ⟨a, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    have pair (a b : Fin 4) : typeF4RootPairing.pairingIn ℤ
        (typeF4RootPairing_baseEquiv a) (typeF4RootPairing_baseEquiv b) =
          typeF4CartanMatrix a b := typeF4RootPairing_base_cartan_apply a b
    fin_cases a
    · exact ⟨typeF4RootPairing_baseEquiv 1, by rw [pair]; norm_num [typeF4CartanMatrix]⟩
    · exact ⟨typeF4RootPairing_baseEquiv 0, by rw [pair]; norm_num [typeF4CartanMatrix]⟩
    · exact ⟨typeF4RootPairing_baseEquiv 3, by rw [pair]; norm_num [typeF4CartanMatrix, Fin.ext_iff]⟩
    · exact ⟨typeF4RootPairing_baseEquiv 2, by rw [pair]; norm_num [typeF4CartanMatrix, Fin.ext_iff]⟩
  have route (w : List typeF4RootPairing_base.support) (k : typeF4RootPairing_base.support) :
      ∃ j : typeF4RootPairing_base.support,
        (typeF4RootPairing.pairingIn ℤ (reflectionWord (P := typeF4RootPairing) w k) j :
          CoefficientField m) ≠ 0 := by
    induction w with
    | nil => exact simple k
    | cons i w ih =>
      by_contra! hn
      obtain ⟨j, hj⟩ := ih
      have hi := hn i
      have h := hn j
      simp only [reflectionWord, pairingIn_reflection] at hi h
      rw [show typeF4RootPairing_base.cartanMatrix i i = 2 by simp] at hi
      simp only [Int.cast_sub, Int.cast_mul,
        Int.cast_ofNat, CharTwo.two_eq_zero, zero_mul, sub_zero] at hi
      apply hj
      simpa only [Int.cast_sub, Int.cast_mul, hi, mul_zero, sub_zero] using h
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  simpa only [z.target] using route z.word z.simple

/-- The root-sum commutator has the prescribed action on every Cartan column. -/
lemma root_commutator_on_cartan (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r)
    (j : typeF4RootPairing_base.support) :
    (dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
      coordinateOperator m (Sum.inr r) * dividedPower m i 1) *ᵥ Pi.single (Sum.inl j) 1 =
        ((typeF4RootPairing.chainBotCoeff i r + 1 : CoefficientField m) •
          coordinateOperator m (Sum.inr s)) *ᵥ Pi.single (Sum.inl j) 1 := by
  rw [dividedPower_one_eq_coordinateOperator]
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, coordinateOperator_mulVec_cartan,
    Matrix.mulVec_smul, Matrix.smul_mulVec]
  rw [coordinateOperator_mulVec_root_add m i r s h,
    coordinateOperator_mulVec_root_add m r i s (h.trans (add_comm _ _)),
    chainBotCoeff_comm_of_root_add r i s (h.trans (add_comm _ _))]
  rw [RootPairing.pairingIn_eq_add_of_root_eq_add (S := ℤ) h, Int.cast_add]
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

/-- Cartan columns determine the coefficient of a commutator in the sum-root line. -/
lemma positive_root_commutator_add_of_mem_line (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r)
    (hline : ∃ c : CoefficientField m,
      dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
        coordinateOperator m (Sum.inr r) * dividedPower m i 1 =
          c • coordinateOperator m (Sum.inr s)) :
    dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
      coordinateOperator m (Sum.inr r) * dividedPower m i 1 =
        (typeF4RootPairing.chainBotCoeff i r + 1 : CoefficientField m) •
          coordinateOperator m (Sum.inr s) := by
  obtain ⟨c, hc⟩ := hline
  obtain ⟨j, hj⟩ := exists_pairingIn_cast_ne_zero m s
  have hu := root_commutator_on_cartan m i r s h j
  rw [hc] at hu
  simp only [Matrix.smul_mulVec, coordinateOperator_mulVec_cartan] at hu
  have hv := congrFun hu (Sum.inr s)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hv
  rw [hc, mul_right_cancel₀ hj hv]

end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
