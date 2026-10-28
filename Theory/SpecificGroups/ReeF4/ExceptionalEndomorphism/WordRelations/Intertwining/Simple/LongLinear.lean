module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.LowDegrees
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# The long simple-root linear comparison

For a long simple root, the quotient-to-ideal map intertwines Geck's linear
operator with the operator at its exceptional short image. On root coordinates,
a root sum with both summands and result of the same length is a reflection string with
coefficient one. Reflection equivariance and transposition of the Cartan pairing
therefore identify the long strings with the short strings. Mixed coordinate
blocks vanish by the root-length restrictions and the even Cartan and Geck
coefficients in characteristic two.

This proves the linear coefficient identity for the actual integral operators
in `F4IntegralChevalleyRepresentation`; `rootDividedPower_simple` identifies them
with the routed root-curve coefficients. The exceptional permutation is the
one constructed in `RootDuality`, in the convention of Aschbacher–Smith,
Remark A.2.4. No intertwining or exceptional group homomorphism is assumed.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix
namespace ReeF4.WordRelations

private lemma norm_bounds (r : typeF4Roots) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr]; norm_num
  · rw [isShortRoot_norm r hr]; norm_num

private lemma same_length_pairing {i j : typeF4Roots}
    (hij : IsLongRoot i ↔ IsLongRoot j) :
    typeF4RootPairing.pairingIn ℤ i j = typeF4RootPairing.pairingIn ℤ j i := by
  apply Int.cast_injective (α := ℝ)
  change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _
  rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing.algebraMap_pairingIn,
    typeF4RootPairing_pairing, typeF4RootPairing_pairing]
  by_cases hi : IsLongRoot i
  · rw [typeF4CorootScale_of_pair i hi, typeF4CorootScale_of_pair j (hij.mp hi)]
    exact congrArg (fun x : ℝ => 1 * x) (dotProduct_comm _ _)
  · rw [typeF4CorootScale_of_not_pair i hi,
      typeF4CorootScale_of_not_pair j (fun hj => hi (hij.mpr hj))]
    exact congrArg (fun x : ℝ => 2 * x) (dotProduct_comm _ _)

private lemma same_length_sum {i j k : typeF4Roots}
    (hij : IsLongRoot i ↔ IsLongRoot j) (hik : IsLongRoot i ↔ IsLongRoot k)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    typeF4RootPairing.pairingIn ℤ j i = -1 ∧ typeF4RootPairing.chainBotCoeff i j = 0 := by
  have hn : dot k.val k.val = dot i.val i.val + dot j.val j.val + 2 * dot j.val i.val := by
    rw [show k.val = i.val + j.val from h]
    change (i.val + j.val) ⬝ᵥ (i.val + j.val) = _
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm i.val j.val]
    dsimp only [dot, dotProduct]
    ring
  have hnj : dot j.val j.val = dot i.val i.val := by
    by_cases hi : IsLongRoot i
    · rw [isLongRoot_norm i hi, isLongRoot_norm j (hij.mp hi)]
    · rw [isShortRoot_norm i hi, isShortRoot_norm j (fun hj => hi (hij.mpr hj))]
  have hnk : dot k.val k.val = dot i.val i.val := by
    by_cases hi : IsLongRoot i
    · rw [isLongRoot_norm i hi, isLongRoot_norm k (hik.mp hi)]
    · rw [isShortRoot_norm i hi, isShortRoot_norm k (fun hk => hi (hik.mpr hk))]
  rw [hnj, hnk] at hn
  constructor
  · apply Int.cast_injective (α := ℝ)
    change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing]
    by_cases hi : IsLongRoot i
    · rw [typeF4CorootScale_of_pair i hi, one_mul]
      rw [isLongRoot_norm i hi] at hn
      norm_num
      linarith
    · rw [typeF4CorootScale_of_not_pair i hi]
      rw [isShortRoot_norm i hi] at hn
      norm_num
      linarith
  · apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
    right
    rintro ⟨l, hl⟩
    have hnl : dot l.val l.val = dot j.val j.val + dot i.val i.val -
        2 * dot j.val i.val := by
      rw [show l.val = j.val - i.val from hl]
      change (j.val - i.val) ⬝ᵥ (j.val - i.val) = _
      simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm i.val j.val]
      dsimp only [dot, dotProduct]
      ring
    rw [hnj] at hnl
    linarith [(norm_bounds i).1, (norm_bounds l).2]

private lemma reflection_of_pairing_neg_one {i j : typeF4Roots}
    (h : typeF4RootPairing.pairingIn ℤ j i = -1) :
    typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i j) =
      typeF4RootPairing.root i + typeF4RootPairing.root j := by
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root,
    ← typeF4RootPairing.algebraMap_pairingIn ℤ, h]
  simp [add_comm]

private lemma dual_sum_of_same_length {i j k : typeF4Roots}
    (hij : IsLongRoot i ↔ IsLongRoot j) (hik : IsLongRoot i ↔ IsLongRoot k)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    typeF4RootPairing.root (exceptionalRootPermutation k) =
      typeF4RootPairing.root (exceptionalRootPermutation i) +
        typeF4RootPairing.root (exceptionalRootPermutation j) := by
  have hp := (same_length_sum hij hik h).1
  have hk : k = typeF4RootPairing.reflectionPerm i j :=
    typeF4RootPairing.root.injective (h.trans (reflection_of_pairing_neg_one hp).symm)
  rw [hk, exceptionalRootPermutation_reflection]
  apply reflection_of_pairing_neg_one
  rw [exceptionalRootPermutation_pairingIn, same_length_pairing hij]
  exact hp

private lemma eMatrix_dual_long_coordinates
    (i : typeF4RootPairing_base.support) (hi : IsLongRoot i.val)
    (a b : Coordinate) (ha : ¬IsShortCoordinate a) (hb : ¬IsShortCoordinate b) :
    eMatrix (P := typeF4RootPairing) i a b =
      eMatrix (P := typeF4RootPairing) (simplePermutation i)
        (coordinatePermutation a) (coordinatePermutation b) := by
  classical
  let := typeF4RootPairing.indexNeg
  rcases a with a | a <;> rcases b with b | b
  · simp [eMatrix]
  · simp only [coordinatePermutation_inl, coordinatePermutation_inr, eMatrix,
      Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    change (if a = i ∧ b = -i.val then (1 : ℤ) else 0) =
      if simplePermutation a = simplePermutation i ∧
        exceptionalRootPermutation b = -(simplePermutation i).val then 1 else 0
    rw [simplePermutation_val, ← exceptionalRootPermutation_neg]
    simp only [Equiv.apply_eq_iff_eq]
  · have hcartan : typeF4RootPairing_base.cartanMatrix
        (simplePermutation i) (simplePermutation b) =
        typeF4RootPairing_base.cartanMatrix i b := by
      change typeF4RootPairing.pairingIn ℤ (simplePermutation i).val
        (simplePermutation b).val = typeF4RootPairing.pairingIn ℤ i.val b.val
      rw [simplePermutation_val, simplePermutation_val, exceptionalRootPermutation_pairingIn]
      exact same_length_pairing (iff_of_true (not_not.mp hb) hi)
    simp [eMatrix, hcartan, simplePermutation_val]
  · have hal : IsLongRoot a := not_not.mp ha
    have hbl : IsLongRoot b := not_not.mp hb
    have hdi : IsShortRoot (exceptionalRootPermutation i.val) :=
      (exceptionalRootPermutation_long_iff i.val).mp hi
    have hda : IsShortRoot (exceptionalRootPermutation a) :=
      (exceptionalRootPermutation_long_iff a).mp hal
    have hdb : IsShortRoot (exceptionalRootPermutation b) :=
      (exceptionalRootPermutation_long_iff b).mp hbl
    have heq : typeF4RootPairing.root a =
        typeF4RootPairing.root i.val + typeF4RootPairing.root b ↔
        typeF4RootPairing.root (exceptionalRootPermutation a) =
          typeF4RootPairing.root (exceptionalRootPermutation i.val) +
            typeF4RootPairing.root (exceptionalRootPermutation b) := by
      constructor
      · exact dual_sum_of_same_length (iff_of_true hi hbl) (iff_of_true hi hal)
      · intro h
        simpa only [exceptionalRootPermutation_involutive a,
          exceptionalRootPermutation_involutive i.val, exceptionalRootPermutation_involutive b] using
          dual_sum_of_same_length (iff_of_false hdi hdb) (iff_of_false hdi hda) h
    simp only [coordinatePermutation_inr, eMatrix, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply, simplePermutation_val]
    by_cases h : typeF4RootPairing.root a =
        typeF4RootPairing.root i.val + typeF4RootPairing.root b
    · rw [if_pos h, if_pos (heq.mp h),
        (same_length_sum (iff_of_true hi hbl) (iff_of_true hi hal) h).2,
        (same_length_sum (iff_of_false hdi hdb) (iff_of_false hdi hda) (heq.mp h)).2]
    · rw [if_neg h, if_neg (fun hd => h (heq.mpr hd))]

private lemma eMatrix_long_short_column {K : Type*} [CommRing K] [CharP K 2]
    (i : typeF4RootPairing_base.support) (hi : IsLongRoot i.val)
    (a b : Coordinate) (ha : ¬IsShortCoordinate a) (hb : IsShortCoordinate b) :
    (eMatrix (P := typeF4RootPairing) i a b : K) = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  rcases a with a | a <;> rcases b with b | b
  · simp [eMatrix]
  · have hne : b ≠ -i.val := by
      rintro rfl
      exact hb ((isLongRoot_neg_iff i.val).mpr hi)
    simp only [eMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    rw [if_neg (show ¬(a = i ∧ b = -i.val) from fun h => hne h.2), Int.cast_zero]
  · rcases ShortOperators.long_short_cartan i b (not_not.mpr hi) hb with h | h
    · simp [eMatrix, h]
    · simp only [eMatrix, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
      split_ifs <;> simp [h, CharTwo.two_eq_zero]
  · have hal : IsLongRoot a := not_not.mp ha
    have hne : typeF4RootPairing.root a ≠
        typeF4RootPairing.root i.val + typeF4RootPairing.root b := by
      intro h
      exact (ShortOperators.short_add_long b i.val a hb hal
        (by simpa only [add_comm] using h)).1 hi
    simp only [eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, if_neg hne, Int.cast_zero]

/-- The long simple-root linear coefficient comparison over any commutative
ring of characteristic two, in particular every Ree coefficient field. -/
theorem quotientToIdeal_eDividedPower_one_long {K : Type*} [CommRing K] [CharP K 2]
    (i : typeF4RootPairing_base.support) (hi : IsLongRoot i.val) :
    quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 1) =
      specializeMatrix (S := K)
        (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) * quotientToIdeal := by
  classical
  have hdi : IsShortRoot (simplePermutation i).val := by
    rw [simplePermutation_val]
    exact (exceptionalRootPermutation_long_iff i.val).mp hi
  have hzero := (quotientToIdeal_mul_eq_zero_iff _).mp
    (quotientToIdeal_eDividedPower_one_short (K := K) (simplePermutation i) hdi)
  ext a b
  rw [quotientToIdeal_mul, mul_quotientToIdeal]
  by_cases ha : IsShortCoordinate a
  · rw [if_pos ha]
    have hpa : ¬IsShortCoordinate (coordinatePermutation a) := by
      simpa only [coordinatePermutation_short_iff, not_not] using ha
    by_cases hb : IsShortCoordinate b
    · rw [if_pos hb]
      exact eMatrix_long_short_column i hi (coordinatePermutation a) b hpa hb
    · rw [if_neg hb]
      simp only [specializeMatrix, Matrix.map_apply, eDividedPower_one]
      rw [eMatrix_dual_long_coordinates i hi _ _ hpa hb,
        coordinatePermutation_involutive]
  · rw [if_neg ha]
    by_cases hb : IsShortCoordinate b
    · rw [if_pos hb]
    · rw [if_neg hb]
      exact (hzero a ha (coordinatePermutation b)).symm

end ReeF4.WordRelations
