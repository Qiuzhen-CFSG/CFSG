module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.RootStrings
public import Mathlib.Algebra.CharP.Two

/-!
# Vanishing and quadratic coefficients for the F4 exceptional comparison

Two-step strings in a long direction, or starting at a short root, join only
opposite roots. Their divided-power coefficient is one. This proves the
quadratic comparison for long simple roots and the vanishing of long quadratic
operators on the short ideal. A short simple operator has coefficient two in
every long row it reaches, so its action on the long quotient vanishes in
characteristic two.

These are unconditional identities for the actual integral Geck matrices,
specialized to the coefficient ring. They supply all auxiliary coefficients
in the polynomial reduction; the remaining linear long-root and quadratic
short-root comparisons are separate inputs. The root and matrix conventions
are those of `RootDuality` and `F4IntegralChevalleyRepresentation`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix
namespace ReeF4.WordRelations

lemma eDividedPower_two_root_entry (i : typeF4RootPairing_base.support)
    (j k : typeF4Roots) (hi : IsLongRoot i.val ∨ IsShortRoot j) :
    letI := typeF4RootPairing.indexNeg
    eDividedPower (P := typeF4RootPairing) i 2 (Sum.inr k) (Sum.inr j) =
      if k = i.val ∧ j = -i.val then 1 else 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  have hneg (r : typeF4Roots) : typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have heq : typeF4RootPairing.root k =
      typeF4RootPairing.root j + (2 : ℕ) • typeF4RootPairing.root i ↔
      k = i.val ∧ j = -i.val := by
    constructor
    · intro h
      have h' : k.val = j.val + (2 : ℝ) • i.val.val := by
        simpa only [typeF4RootPairing_root, ofNat_smul_eq_nsmul] using h
      have hh := hi.elim (fun hi => root_add_two_of_long hi h')
        (fun hj => root_add_two_of_short_column hj h')
      refine ⟨Subtype.ext hh.2, ?_⟩
      apply typeF4RootPairing.root.injective
      simpa only [hneg, typeF4RootPairing_root] using hh.1
    · rintro ⟨rfl, rfl⟩
      rw [hneg]
      module
  by_cases hh : k = i.val ∧ j = -i.val
  · rcases hh with ⟨rfl, rfl⟩
    have hbot : typeF4RootPairing.chainBotCoeff i.val (-i.val) = 0 := by
      apply RootPairing.chainBotCoeff_of_not_linearIndependent
      rw [hneg]
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, 1, by simp, by simp⟩
    dsimp only [eDividedPower, Matrix.of_apply]
    rw [if_pos (heq.mpr ⟨rfl, rfl⟩), hbot]
    norm_num
  · dsimp only [eDividedPower, Matrix.of_apply]
    rw [if_neg (fun h => hh (heq.mp h)), if_neg hh]

lemma specialize_eDividedPower_two_apply {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (a b : Coordinate)
    (hi : IsLongRoot i.val ∨ IsShortCoordinate b) :
    letI := typeF4RootPairing.indexNeg
    specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) a b =
      if a = Sum.inr i.val ∧ b = Sum.inr (-i.val) then 1 else 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  rcases a with a | a <;> rcases b with b | b
  · simp [specializeMatrix, eDividedPower]
  · simp [specializeMatrix, eDividedPower]
  · simp [specializeMatrix, eDividedPower]
  · change (eDividedPower (P := typeF4RootPairing) i 2 (Sum.inr a) (Sum.inr b) : K) = _
    rw [eDividedPower_two_root_entry i b a hi]
    simp

lemma quotientToIdeal_eDividedPower_one_short {K : Type*} [CommRing K] [CharP K 2]
    (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val) :
    quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 1) = 0 := by
  apply (quotientToIdeal_mul_eq_zero_iff _).mpr
  intro a ha b
  simp only [specializeMatrix, Matrix.map_apply, eDividedPower_one]
  rcases a with a | a <;> rcases b with b | b
  · simp [eMatrix]
  · have hai : a ≠ i := by rintro rfl; exact ha hi
    simp [eMatrix, hai]
  · have hai : a ≠ i.val := by rintro rfl; exact ha hi
    simp [eMatrix, hai]
  · have hal : IsLongRoot a := not_not.mp ha
    by_cases h : typeF4RootPairing.root a =
        typeF4RootPairing.root i.val + typeF4RootPairing.root b
    · have hb := chainBotCoeff_short_add_long hi hal h
      simp only [eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, if_pos h, hb]
      norm_num
      exact CharTwo.two_eq_zero
    · simp only [eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, if_neg h, map_zero]

lemma eDividedPower_two_long_mul_quotientToIdeal {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (hi : IsLongRoot i.val) :
    specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) * quotientToIdeal = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  apply (mul_quotientToIdeal_eq_zero_iff _).mpr
  intro b hb a
  rw [specialize_eDividedPower_two_apply i a b (Or.inr hb)]
  have hne : b ≠ Sum.inr (-i.val) := by
    rintro rfl
    exact hb ((isLongRoot_neg_iff i.val).mpr hi)
  simp only [hne, and_false, if_false]

lemma quotientToIdeal_eDividedPower_two_long {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (hi : IsLongRoot i.val) :
    quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) =
      specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 2) *
        quotientToIdeal := by
  classical
  let := typeF4RootPairing.indexNeg
  have hdi : IsShortRoot (simplePermutation i).val := by
    rw [simplePermutation_val]
    exact (exceptionalRootPermutation_long_iff i.val).mp hi
  have hp (a b : Coordinate) : coordinatePermutation a = b ↔ a = coordinatePermutation b := by
    constructor
    · intro h
      rw [← h, coordinatePermutation_involutive a]
    · intro h
      rw [h, coordinatePermutation_involutive b]
  have hin : coordinatePermutation (Sum.inr i.val) = Sum.inr (simplePermutation i).val := by
    rw [coordinatePermutation_inr, simplePermutation_val]
  have hneg : coordinatePermutation (Sum.inr (-(simplePermutation i).val)) = Sum.inr (-i.val) := by
    rw [coordinatePermutation_inr, exceptionalRootPermutation_neg, simplePermutation_val,
      exceptionalRootPermutation_involutive]
  ext a b
  rw [quotientToIdeal_mul, mul_quotientToIdeal]
  rw [specialize_eDividedPower_two_apply i _ _ (Or.inl hi)]
  by_cases hb : IsShortCoordinate b
  · rw [if_pos hb]
    have hne : b ≠ Sum.inr (-i.val) := by
      rintro rfl
      exact hb ((isLongRoot_neg_iff i.val).mpr hi)
    simp only [hne, and_false, if_false, ite_self]
  · rw [if_neg hb, specialize_eDividedPower_two_apply _ _ _
        (Or.inr ((coordinatePermutation_short_iff b).mpr hb))]
    simp only [hp, hin, hneg]
    by_cases ha : IsShortCoordinate a
    · rw [if_pos ha]
    · rw [if_neg ha]
      have hne : a ≠ Sum.inr (simplePermutation i).val := by
        rintro rfl
        exact ha hdi
      simp only [hne, false_and, if_false]

end ReeF4.WordRelations
