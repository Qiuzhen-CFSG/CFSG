module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootColumns

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.RootKernel.DetectionGeometry

/-!
# Root coordinates of the common kernel of short F4 operators

For each root `r`, a short root `s` detects its coefficient in the row `s + r`,
with root-string coefficient one. Other root columns cannot contribute to this
row: root addition is injective, absent sums give zero columns, and opposite
roots give Cartan vectors. The latter support claim follows directly by
induction over the actual integral Tits transport.

The only conditional input is the stated Cartan-column formula. It ensures
that Cartan columns contribute only to row `s`, which differs from `s + r`.
Thus a vector killed by every short-root operator has all root coordinates
zero. This does not assert that its Cartan coordinates vanish.

The matrices and root-string identities are those of Geck's integral
Cartan-plus-root construction; see Steinberg, *Lectures on Chevalley Groups*,
the integral admissible lattice and its root operators.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix

namespace ReeF4.WordRelations.ShortOperators

private lemma titsWord_u_root (w : List typeF4RootPairing_base.support) (j : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (titsWord (P := typeF4RootPairing) w *ᵥ u j) (Sum.inr r) = 0 := by
  induction w generalizing r with
  | nil => simp [titsWord, u]
  | cons i w ih =>
    rw [titsWord, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    rcases k with k | k
    · have h := congrFun (titsLift_mulVec_u (P := typeF4RootPairing) i k) (Sum.inr r)
      simp only [u, Matrix.mulVec_single_one, Matrix.col_apply] at h
      have hz : titsLift (P := typeF4RootPairing) i (Sum.inr r) (Sum.inl k) = 0 := by simpa using h
      rw [hz, zero_mul]
    · rw [ih k, mul_zero]

private lemma rootCartanVector_root (s r : typeF4Roots) :
    rootCartanVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) s (Sum.inr r) = 0 := by
  exact titsWord_u_root _ _ _

private lemma rootOperator_opposite_root_entry {K : Type*} [CommRing K] [CharP K 2]
    (s r : typeF4Roots) :
    let := typeF4RootPairing.indexNeg
    ((Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
      (Int.castRingHom K) *ᵥ Pi.single (Sum.inr (-s) : Coordinate) 1) (Sum.inr r) = 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  have hz : (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s *ᵥ
      rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)) (Sum.inr r) = 0 := by
    by_cases hs : typeF4RootPairing_base.IsPos s
    · rw [rootOperator_mulVec_opposite s hs, rootCartanVector_root]
    · have hn := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base s).mpr hs
      have he := rootOperator_neg_mulVec (P := typeF4RootPairing)
        (b := typeF4RootPairing_base) (-s) hn
      simp only [neg_neg] at he
      rw [he, rootCartanVector_root]
  have he := (Int.castRingHom K).map_mulVec
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s)
    (rootVector (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-s)) (Sum.inr r)
  rw [hz, map_zero, rootVector_cast] at he
  exact he.symm

private lemma rootOperator_detector_row {K : Type*} [CommRing K] [CharP K 2]
    (s r k : typeF4Roots)
    (hadd : typeF4RootPairing.root k = typeF4RootPairing.root s + typeF4RootPairing.root r)
    (hcoeff : typeF4RootPairing.chainBotCoeff s r = 0)
    (hcartan : ∀ j : typeF4RootPairing_base.support,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : K) • Pi.single (Sum.inr s : Coordinate) 1)
    (c : Coordinate) :
    (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
      (Int.castRingHom K) (Sum.inr k) c = if c = Sum.inr r then 1 else 0 := by
  classical
  let := typeF4RootPairing.indexNeg
  have hks : k ≠ s := by
    intro he
    have hz : typeF4RootPairing.root r = 0 := by
      rw [he] at hadd
      exact (add_eq_left.mp hadd.symm)
    exact typeF4RootPairing.ne_zero r hz
  rcases c with j | j
  · have he := congrFun (hcartan j) (Sum.inr k)
    simpa [Matrix.mulVec_single_one, hks] using he
  · by_cases hj : j = r
    · subst j
      have he := congrFun (rootOperator_rootColumn_add (K := K) s r k hadd) (Sum.inr k)
      simpa [Matrix.mulVec_single_one, hcoeff] using he
    · have hz :
          ((Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
            (Int.castRingHom K) *ᵥ Pi.single (Sum.inr j : Coordinate) 1) (Sum.inr k) = 0 := by
        by_cases hopp : j = -s
        · subst j
          exact rootOperator_opposite_root_entry s k
        · by_cases hmem : typeF4RootPairing.root s + typeF4RootPairing.root j ∈
              Set.range typeF4RootPairing.root
          · obtain ⟨t, ht⟩ := hmem
            have hkt : k ≠ t := by
              intro h
              apply hj
              apply typeF4RootPairing.root.injective
              rw [← h] at ht
              exact add_left_cancel (ht.symm.trans hadd)
            have he := congrFun (rootOperator_rootColumn_add (K := K) s j t ht) (Sum.inr k)
            simpa [hkt] using he
          · have he := congrFun (rootOperator_rootColumn_zero (K := K) s j hopp hmem) (Sum.inr k)
            simpa using he
      simpa [Matrix.mulVec_single_one, hj] using hz

private lemma rootOperator_detector_mulVec {K : Type*} [CommRing K] [CharP K 2]
    (s r k : typeF4Roots)
    (hadd : typeF4RootPairing.root k = typeF4RootPairing.root s + typeF4RootPairing.root r)
    (hcoeff : typeF4RootPairing.chainBotCoeff s r = 0)
    (hcartan : ∀ j : typeF4RootPairing_base.support,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : K) • Pi.single (Sum.inr s : Coordinate) 1)
    (x : Coordinate → K) :
    ((Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
      (Int.castRingHom K) *ᵥ x) (Sum.inr k) = x (Sum.inr r) := by
  classical
  simp only [Matrix.mulVec, dotProduct, rootOperator_detector_row s r k hadd hcoeff hcartan]
  simp
/-- The common kernel of the actual short-root operators has no root
coordinates, assuming the displayed Cartan-column formula. -/
theorem root_coordinates_eq_zero_of_common_kernel {K : Type*} [CommRing K] [CharP K 2]
    (hcartan : ∀ s : typeF4Roots, IsShortRoot s → ∀ j : typeF4RootPairing_base.support,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : K) • Pi.single (Sum.inr s : Coordinate) 1)
    (x : Coordinate → K)
    (hkernel : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom K) *ᵥ x = 0)
    (r : typeF4Roots) : x (Sum.inr r) = 0 := by
  obtain ⟨s, k, hs, -, hadd, hcoeff⟩ := exists_short_detector r
  have he := rootOperator_detector_mulVec s r k hadd hcoeff (hcartan s hs) x
  rw [hkernel s hs] at he
  exact he.symm

/-- Root-coordinate elimination over every Ree coefficient field, with exactly
the Cartan-column premise to be discharged by the common-kernel assembly. -/
theorem coefficientField_root_coordinates_eq_zero_of_common_kernel (m : ℕ)
    (hcartan : ∀ s : typeF4Roots, IsShortRoot s → ∀ j : typeF4RootPairing_base.support,
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) *ᵥ Pi.single (Sum.inl j : Coordinate) 1 =
      (typeF4RootPairing.pairingIn ℤ s j : CoefficientField m) •
        Pi.single (Sum.inr s : Coordinate) 1)
    (x : Coordinate → CoefficientField m)
    (hkernel : ∀ s : typeF4Roots, IsShortRoot s →
      (Theory.AlgebraicGroup.F4Chevalley.integralOperators.rootOperator s).map
        (Int.castRingHom (CoefficientField m)) *ᵥ x = 0)
    (r : typeF4Roots) : x (Sum.inr r) = 0 :=
  root_coordinates_eq_zero_of_common_kernel hcartan x hkernel r

end ReeF4.WordRelations.ShortOperators
