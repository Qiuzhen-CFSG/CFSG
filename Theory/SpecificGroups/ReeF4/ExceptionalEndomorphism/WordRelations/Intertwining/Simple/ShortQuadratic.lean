module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.LowDegrees
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality

/-!
# The short simple-root quadratic comparison

Exceptional root duality carries a two-step string in a short direction with
long endpoints to a one-step string in the dual long direction. The endpoints
are reflections: the relevant Cartan pairings are respectively minus two and
minus one, and the actual exceptional permutation transposes the pairing and
commutes with reflection. Both integral Geck coefficients are one, since a
predecessor would produce an impossible longer root string.

The remaining Cartan/root blocks vanish by root lengths and the even mixed
Cartan coefficients in characteristic two. This proves the quadratic-to-linear
coefficient identity for the integral matrices in
`F4IntegralChevalleyRepresentation`; `rootDividedPower_simple` identifies these
with the actual routed coefficients. The root convention is that of
`RootDuality` (Aschbacher–Smith, Remark A.2.4). No exceptional group homomorphism
or intertwining identity is assumed.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical Matrix
namespace ReeF4.WordRelations

private lemma norm_add (i j : Vec 4) :
    dot (i + j) (i + j) = dot i i + dot j j + 2 * dot i j := by
  change (i + j) ⬝ᵥ (i + j) = _
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm j i]
  dsimp only [dot, dotProduct]
  ring

private lemma norm_add_two (i j : Vec 4) :
    dot (j + (2 : ℝ) • i) (j + (2 : ℝ) • i) =
      dot j j + 4 * dot i i + 4 * dot i j := by
  change (j + (2 : ℝ) • i) ⬝ᵥ (j + (2 : ℝ) • i) = _
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm j i]
  dsimp only [dot, dotProduct]
  ring

private lemma dual_pairing (r s : typeF4Roots) :
    typeF4RootPairing.pairing (exceptionalRootPermutation r) (exceptionalRootPermutation s) =
      typeF4RootPairing.pairing s r := by
  rw [← typeF4RootPairing.algebraMap_pairingIn ℤ,
    exceptionalRootPermutation_pairingIn, typeF4RootPairing.algebraMap_pairingIn]

private lemma long_add_short_isShort {i j k : typeF4Roots}
    (hi : IsLongRoot i) (hj : IsShortRoot j)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    IsShortRoot k := by
  intro hk
  have hn := norm_add i.val j.val
  rw [← show k.val = i.val + j.val from h, isLongRoot_norm k hk,
    isLongRoot_norm i hi, isShortRoot_norm j hj] at hn
  obtain ⟨z, hz⟩ := typeF4RootPairing_pairing_eq_intCast j i
  rw [typeF4RootPairing_pairing, typeF4CorootScale_of_pair i hi, one_mul] at hz
  have hc : (2 : ℝ) * z = -1 := by rw [hz, show dot j.val i.val = dot i.val j.val from dotProduct_comm _ _]; linarith
  have hc' : (2 : ℤ) * z = -1 := by exact_mod_cast hc
  omega

private lemma two_step_duality {i j k : typeF4Roots}
    (hi : IsShortRoot i) (hj : IsLongRoot j) (hk : IsLongRoot k) :
    typeF4RootPairing.root k = typeF4RootPairing.root j + (2 : ℕ) • typeF4RootPairing.root i ↔
      typeF4RootPairing.root (exceptionalRootPermutation k) =
        typeF4RootPairing.root (exceptionalRootPermutation i) +
          typeF4RootPairing.root (exceptionalRootPermutation j) := by
  have hi' := (exceptionalRootPermutation_short_iff i).mp hi
  have hj' := (exceptionalRootPermutation_long_iff j).mp hj
  have hk' := (exceptionalRootPermutation_long_iff k).mp hk
  constructor
  · intro h
    have he : k.val = j.val + (2 : ℝ) • i.val := by
      simpa only [typeF4RootPairing_root, ofNat_smul_eq_nsmul] using h
    have hn := norm_add_two i.val j.val
    rw [← he, isLongRoot_norm k hk, isLongRoot_norm j hj, isShortRoot_norm i hi] at hn
    have hd : dot i.val j.val = -1 := by linarith
    have hp : typeF4RootPairing.pairing j i = -2 := by
      rw [typeF4RootPairing_pairing, typeF4CorootScale_of_not_pair i hi,
        show dot j.val i.val = dot i.val j.val from dotProduct_comm _ _, hd]
      norm_num
    have hp' : typeF4RootPairing.pairing i j = -1 := by
      rw [typeF4RootPairing_pairing, typeF4CorootScale_of_pair j hj, hd, one_mul]
    have hr : k = typeF4RootPairing.reflectionPerm i j := by
      apply typeF4RootPairing.root.injective
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root, hp]
      change k.val = j.val - (-2 : ℝ) • i.val
      rw [he]; module
    rw [hr, exceptionalRootPermutation_reflection, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_root, dual_pairing, hp']
    module
  · intro h
    have hn := norm_add (exceptionalRootPermutation i).val (exceptionalRootPermutation j).val
    rw [← show (exceptionalRootPermutation k).val =
        (exceptionalRootPermutation i).val + (exceptionalRootPermutation j).val from h,
      isShortRoot_norm _ hk', isLongRoot_norm _ hi', isShortRoot_norm _ hj'] at hn
    have hd : dot (exceptionalRootPermutation i).val (exceptionalRootPermutation j).val = -1 := by linarith
    have hp : typeF4RootPairing.pairing (exceptionalRootPermutation j)
        (exceptionalRootPermutation i) = -1 := by
      rw [typeF4RootPairing_pairing, typeF4CorootScale_of_pair _ hi', one_mul,
        show dot (exceptionalRootPermutation j).val (exceptionalRootPermutation i).val =
          dot (exceptionalRootPermutation i).val (exceptionalRootPermutation j).val from dotProduct_comm _ _, hd]
    have hp' : typeF4RootPairing.pairing j i = -2 := by
      rw [← dual_pairing i j, typeF4RootPairing_pairing,
        typeF4CorootScale_of_not_pair _ hj', hd]
      norm_num
    have hr : k = typeF4RootPairing.reflectionPerm i j := by
      apply exceptionalRootPermutation.injective
      rw [exceptionalRootPermutation_reflection]
      apply typeF4RootPairing.root.injective
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root, hp, h]
      module
    rw [hr, typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root, hp']
    module

private lemma botCoeff_two_step {i j k : typeF4Roots}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root j + (2 : ℕ) • typeF4RootPairing.root i) :
    typeF4RootPairing.chainBotCoeff i j = 0 := by
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l, hl⟩
  apply root_ne_add_three_nsmul i l k
  rw [h, hl]
  module

private lemma botCoeff_long_step {i j k : typeF4Roots} (hi : IsLongRoot i)
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    typeF4RootPairing.chainBotCoeff i j = 0 := by
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l, hl⟩
  have he : k.val = l.val + (2 : ℝ) • i.val := by
    change l.val = j.val - i.val at hl
    change k.val = i.val + j.val at h
    rw [h, hl]; module
  have hk := (root_add_two_of_long hi he).2
  apply typeF4RootPairing.ne_zero j
  change j.val = 0
  change k.val = i.val + j.val at h
  rw [hk] at h
  exact add_eq_left.mp h.symm

private lemma cartan_long_short_cast {K : Type*} [CommRing K] [CharP K 2]
    (i j : typeF4RootPairing_base.support) (hi : IsLongRoot i.val) (hj : IsShortRoot j.val) :
    ((|typeF4RootPairing_base.cartanMatrix i j| : ℤ) : K) = 0 := by
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  have hi' : i.val < 2 := (typeF4SimpleRootIndex_mem_pair_iff i).mp hi
  have hj' : ¬j.val < 2 := fun h => hj ((typeF4SimpleRootIndex_mem_pair_iff j).mpr h)
  rw [typeF4RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases j <;> simp_all [typeF4CartanMatrix, CharTwo.two_eq_zero]

private lemma quadratic_linear_root_entry {K : Type*} [Ring K]
    (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val)
    (a b : typeF4Roots) (ha : IsShortRoot a) (hb : IsLongRoot b) :
    specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2)
        (Sum.inr (exceptionalRootPermutation a)) (Sum.inr b) =
      specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1)
        (Sum.inr a) (Sum.inr (exceptionalRootPermutation b)) := by
  have hdi : IsLongRoot (simplePermutation i).val := by
    rw [simplePermutation_val]
    exact (exceptionalRootPermutation_short_iff i.val).mp hi
  have heq : typeF4RootPairing.root (exceptionalRootPermutation a) =
      typeF4RootPairing.root b + (2 : ℕ) • typeF4RootPairing.root i.val ↔
      typeF4RootPairing.root a = typeF4RootPairing.root (simplePermutation i).val +
        typeF4RootPairing.root (exceptionalRootPermutation b) := by
    simpa only [exceptionalRootPermutation_involutive a, simplePermutation_val] using
      two_step_duality hi hb ((exceptionalRootPermutation_short_iff a).mp ha)
  simp only [specializeMatrix, Matrix.map_apply, eDividedPower, eMatrix,
    Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  by_cases h : typeF4RootPairing.root (exceptionalRootPermutation a) =
      typeF4RootPairing.root b + (2 : ℕ) • typeF4RootPairing.root i.val
  · rw [if_pos h, if_pos (heq.mp h), botCoeff_two_step h, botCoeff_long_step hdi (heq.mp h)]
    norm_num
  · rw [if_neg h, if_neg (fun hh => h (heq.mpr hh))]

/-- The short simple-root quadratic coefficient comparison over every
commutative ring of characteristic two, including each Ree coefficient field. -/
theorem quotientToIdeal_eDividedPower_two_short {K : Type*} [CommRing K] [CharP K 2]
    (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val) :
    quotientToIdeal * specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) i 2) =
      specializeMatrix (S := K) (eDividedPower (P := typeF4RootPairing) (simplePermutation i) 1) *
        quotientToIdeal := by
  classical
  let := typeF4RootPairing.indexNeg
  have hdi : IsLongRoot (simplePermutation i).val := by
    rw [simplePermutation_val]
    exact (exceptionalRootPermutation_short_iff i.val).mp hi
  ext a b
  rw [quotientToIdeal_mul, mul_quotientToIdeal]
  rcases a with a | a <;> rcases b with b | b
  · simp [coordinatePermutation_inl, specializeMatrix, eDividedPower, eMatrix]
  · by_cases hb : IsShortRoot b
    · simp [IsShortCoordinate, hb, specializeMatrix, eDividedPower]
    · have hdb := (exceptionalRootPermutation_long_iff b).mp (not_not.mp hb)
      have hne : exceptionalRootPermutation b ≠ -(simplePermutation i).val := by
        intro h
        rw [h] at hdb
        exact hdb ((isLongRoot_neg_iff _).mpr hdi)
      simp only [IsShortCoordinate, if_neg hb, coordinatePermutation_inl, coordinatePermutation_inr,
        specializeMatrix, Matrix.map_apply, eDividedPower, eMatrix, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, map_zero, ite_self]
      change 0 = ((if a = simplePermutation i ∧
        exceptionalRootPermutation b = -(simplePermutation i).val then 1 else 0 : ℤ) : K)
      rw [if_neg (fun h => hne h.2), Int.cast_zero]
  · by_cases hb : IsShortRoot b.val
    · simp [IsShortCoordinate, hb, specializeMatrix, eDividedPower]
    · have hdb : IsShortRoot (simplePermutation b).val := by
        rw [simplePermutation_val]
        exact (exceptionalRootPermutation_long_iff b.val).mp (not_not.mp hb)
      have hc := cartan_long_short_cast (K := K) (simplePermutation i) (simplePermutation b) hdi hdb
      simp [IsShortCoordinate, hb, specializeMatrix, eDividedPower, eMatrix, hc]
  · by_cases hb : IsShortCoordinate (Sum.inr b)
    · rw [if_pos hb]
      by_cases ha : IsShortCoordinate (Sum.inr a)
      · rw [if_pos ha, coordinatePermutation_inr,
          specialize_eDividedPower_two_apply i _ _ (Or.inr hb)]
        have hne : exceptionalRootPermutation a ≠ i.val := by
          intro h
          have hal := (exceptionalRootPermutation_short_iff a).mp ha
          rw [h] at hal
          exact hi hal
        simp [hne]
      · rw [if_neg ha]
    · rw [if_neg hb]
      by_cases ha : IsShortCoordinate (Sum.inr a)
      · rw [if_pos ha, coordinatePermutation_inr, coordinatePermutation_inr]
        exact quadratic_linear_root_entry i hi a b ha (not_not.mp hb)
      · rw [if_neg ha, coordinatePermutation_inr]
        have hdb := (exceptionalRootPermutation_long_iff b).mp (not_not.mp hb)
        have hne : typeF4RootPairing.root a ≠ typeF4RootPairing.root (simplePermutation i).val +
            typeF4RootPairing.root (exceptionalRootPermutation b) := by
          intro h
          exact ha (long_add_short_isShort hdi hdb h)
        simp only [specializeMatrix, Matrix.map_apply, eDividedPower_one, eMatrix,
          Matrix.fromBlocks_apply₂₂, Matrix.of_apply, if_neg hne, map_zero]

end ReeF4.WordRelations
