module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# Image containment for the actual short F4 operators

The short simple operators have no long rows in characteristic two. Tits lifts
preserve the short-coordinate subspace: their root blocks permute root lengths,
and their Cartan blocks have even coefficients from short to long coordinates.
These properties persist under multiplication. Applying them to the defining
Tits conjugations proves image containment for every canonical short-root
operator, without a choice of an alternative route or a matrix table.

Source: Geck's integral Cartan-plus-root construction as formalized in
`IntegralGeckConstruction` and `IntegralAllRootOperators`; see Steinberg,
*Lectures on Chevalley Groups*, the integral admissible-lattice construction.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix

namespace ReeF4.WordRelations.ShortOperators

variable {K : Type*} [CommRing K] [CharP K 2]

lemma eMatrix_image (s : typeF4RootPairing_base.support) (hs : IsShortRoot s.val) :
    ∀ i, ¬IsShortCoordinate i → ∀ j,
      ((eMatrix (P := typeF4RootPairing) s).map (Int.castRingHom K)) i j = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  rintro (i | i) hi (j | j)
  · simp [eMatrix]
  · have hne : i ≠ s := fun h => hi (h ▸ hs)
    simp [eMatrix, hne]
  · have hne : i ≠ s.val := fun h => hi (h ▸ hs)
    simp [eMatrix, hne]
  · simp only [eMatrix, Matrix.map_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    split_ifs with h
    · rw [short_add_long_chainBot s j i hs (not_not.mp hi) h]
      simpa using CharP.cast_eq_zero K 2
    · simp

lemma fMatrix_image (s : typeF4RootPairing_base.support) (hs : IsShortRoot s.val) :
    ∀ i, ¬IsShortCoordinate i → ∀ j,
      ((fMatrix (P := typeF4RootPairing) s).map (Int.castRingHom K)) i j = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  rintro (i | i) hi (j | j)
  · simp [fMatrix]
  · have hne : i ≠ s := fun h => hi (h ▸ hs)
    simp [fMatrix, hne]
  · have hs' : IsShortRoot (-s.val) := (isShortRoot_neg_iff s.val).mpr hs
    have hne : i ≠ -s.val := fun h => hi (h ▸ hs')
    rw [RootPairing.indexNeg_neg] at hne
    simp [fMatrix, hne]
  · simp only [fMatrix, Matrix.map_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    split_ifs with h
    · have h' : typeF4RootPairing.root i = typeF4RootPairing.root (-s.val) +
          typeF4RootPairing.root j := by
        simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
          RootPairing.reflection_apply_self, sub_eq_add_neg, add_comm] using h
      have hc := short_add_long_chainBot (-s.val) j i
        ((isShortRoot_neg_iff s.val).mpr hs) (not_not.mp hi) h'
      rw [RootPairing.indexNeg_neg, RootPairing.chainBotCoeff_reflectionPerm_left] at hc
      rw [hc]
      simpa using CharP.cast_eq_zero K 2
    · simp

/-- A matrix preserves the short-coordinate subspace if its short columns
have no long entries. -/
@[expose] def PreservesShort (A : Matrix Coordinate Coordinate K) : Prop :=
  ∀ i, ¬IsShortCoordinate i → ∀ j, IsShortCoordinate j → A i j = 0

omit [CharP K 2] in
lemma preservesShort_mul (A B : Matrix Coordinate Coordinate K)
    (hA : PreservesShort A) (hB : PreservesShort B) : PreservesShort (A * B) := by
  classical
  intro i hi j hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : IsShortCoordinate k
  · rw [hA i hi k hk, zero_mul]
  · rw [hB k hk j hj, mul_zero]

omit [CharP K 2] in
lemma preservesShort_one : PreservesShort (1 : Matrix Coordinate Coordinate K) := by
  classical
  intro i hi j hj
  have hne : i ≠ j := fun h => hi (h ▸ hj)
  simp [hne]

lemma titsLift_preservesShort (s : typeF4RootPairing_base.support) :
    PreservesShort ((titsLift (P := typeF4RootPairing) s).map (Int.castRingHom K)) := by
  classical
  intro i hi j hj
  rcases j with j | j
  · have hc := congrFun (titsLift_mulVec_u (P := typeF4RootPairing) s j) i
    simp only [u, Matrix.mulVec_single_one, Matrix.col_apply] at hc
    change (Int.castRingHom K) (titsLift s i (Sum.inl j)) = 0
    rw [hc]
    rcases i with i | i
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      by_cases his : i = s
      · subst i
        rcases long_short_cartan s j hi hj with h | h
        · simp [hij, h]
        · simpa [hij, h] using (CharP.cast_eq_zero K 2)
      · simp [hij, his]
    · simp
  · have hc := congrFun (titsLift_mulVec_v (P := typeF4RootPairing) s j) i
    simp only [v, Matrix.mulVec_single_one, Matrix.col_apply] at hc
    change (Int.castRingHom K) (titsLift s i (Sum.inr j)) = 0
    rw [hc]
    have hne : i ≠ Sum.inr (typeF4RootPairing.reflectionPerm s j) := by
      intro h
      apply hi
      rw [h]
      exact (isShortRoot_reflection s j).mpr hj
    simp [hne]

lemma titsWord_preservesShort (w : List typeF4RootPairing_base.support) :
    PreservesShort ((titsWord (P := typeF4RootPairing) w).map (Int.castRingHom K)) := by
  classical
  induction w with
  | nil => simpa [titsWord] using (preservesShort_one (K := K))
  | cons i w ih =>
      simpa only [titsWord, Matrix.map_mul] using
        preservesShort_mul _ _ (titsLift_preservesShort i) ih

omit [CharP K 2] in
lemma mul_image (A B : Matrix Coordinate Coordinate K) (hA : PreservesShort A)
    (hB : ∀ i, ¬IsShortCoordinate i → ∀ j, B i j = 0) :
    ∀ i, ¬IsShortCoordinate i → ∀ j, (A * B) i j = 0 := by
  classical
  intro i hi j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : IsShortCoordinate k
  · rw [hA i hi k hk, zero_mul]
  · rw [hB k hk j, mul_zero]

omit [CharP K 2] in
lemma image_mul (A B : Matrix Coordinate Coordinate K)
    (hA : ∀ i, ¬IsShortCoordinate i → ∀ j, A i j = 0) :
    ∀ i, ¬IsShortCoordinate i → ∀ j, (A * B) i j = 0 := by
  classical
  intro i hi j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [hA i hi k, zero_mul]

lemma transportedMatrix_image (w : List typeF4RootPairing_base.support)
    (A : Matrix Coordinate Coordinate ℤ)
    (hA : ∀ i, ¬IsShortCoordinate i → ∀ j, A.map (Int.castRingHom K) i j = 0) :
    ∀ i, ¬IsShortCoordinate i → ∀ j,
      (transportedMatrix (P := typeF4RootPairing) w A).map (Int.castRingHom K) i j = 0 := by
  simp only [transportedMatrix, Matrix.map_mul]
  exact image_mul _ _ (mul_image _ _ (titsWord_preservesShort w) hA)

/-- Every actual short F4 root operator has image in the short-coordinate
subspace after specialization in characteristic two. -/
lemma rootOperator_image (s : typeF4Roots) (hs : IsShortRoot s) :
    ∀ i, ¬IsShortCoordinate i → ∀ j,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) i j = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  change ∀ i, ¬IsShortCoordinate i → ∀ j,
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s).map
      (Int.castRingHom K) i j = 0
  have hsimple (r : typeF4Roots) (hr : IsShortRoot r) :
      IsShortRoot (rootRoute (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) r).simple.val := by
    apply (isShortRoot_reflectionWord
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word _).mp
    rwa [(rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target]
  by_cases hp : typeF4RootPairing_base.IsPos s
  · rw [rootOperator_of_pos s hp]
    exact transportedMatrix_image _ _ (eMatrix_image _ (hsimple s hs))
  · have hn : typeF4RootPairing_base.IsPos (-s) :=
      (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base s).mpr hp
    have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-s) hn
    simp only [neg_neg] at he
    rw [he]
    exact transportedMatrix_image _ _
      (fMatrix_image _ (hsimple (-s) ((isShortRoot_neg_iff s).mpr hs)))

end ReeF4.WordRelations.ShortOperators
