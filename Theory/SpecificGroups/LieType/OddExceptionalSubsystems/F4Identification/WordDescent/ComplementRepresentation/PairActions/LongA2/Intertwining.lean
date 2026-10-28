module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.LongA2.Lattice
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.DividedPowers
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Curves

/-!
# Equivariance of the long A2 complement injection

The literal long A2 generators are the signed E6 root curves at nodes 2 and 3.
The root-coordinate signs of `ambientMap` are constant along their root strings.
Its Cartan image is killed by both Geck rows, while its Cartan kernel contains
both simple Cartan vectors. These facts prove commutation with the integral
first-order operators on the entire ambient lattice.

Integral factorial cancellation then gives commutation with every divided
power, hence with the polynomial root curves. Scalar extension retains both
signs and the unchanged parameter in every characteristic. Restricting to the
diagram eigenspaces proves `Intertwines`, and the existing word induction gives
the actual long-pair word application. Equivariance itself needs neither
finiteness nor a characteristic restriction; the separate injectivity theorem
uses the nonzero-two hypothesis.

Sources: the common-lattice subsystem construction in GLS3 §2.6.2
(`refs/KGroup/GLS3/chapter2.tex`) and the F4 inclusions used in
Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup Matrix WordDescent
attribute [local instance] Classical.decEq

private theorem simple_fixed (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    typeE6DiagramEquiv.indexEquiv (simpleIndex i : typeE6Roots) = simpleIndex i := by
  rw [typeE6DiagramEquiv_simple]
  rcases hi with rfl | rfl <;>
    simp only [simpleIndex, typeE6DiagramBasePermutation_numbered] <;> rfl

private theorem neg_simple_fixed (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    typeE6DiagramEquiv.indexEquiv
        (typeE6RootPairing.reflectionPerm (simpleIndex i) (simpleIndex i)) =
      typeE6RootPairing.reflectionPerm (simpleIndex i) (simpleIndex i) := by
  let := typeE6RootPairing.indexNeg
  change typeE6DiagramEquiv.indexEquiv (-(simpleIndex i : typeE6Roots)) =
    -(simpleIndex i : typeE6Roots)
  rw [typeE6Diagram_neg, simple_fixed i hi]

private theorem cartanRow_ambientMap (i : Fin 6) (hi : i = 2 ∨ i = 3) (x : Space ℤ) :
    ∑ j : Base.support, |Base.cartanMatrix (simpleIndex i) j| *
      ambientMap ℤ x (.inl j) = 0 := by
  rw [← Equiv.sum_comp typeE6RootPairing_baseEquiv]
  change (∑ j : Fin 6, |Base.cartanMatrix (simpleIndex i) (simpleIndex j)| *
    ambientMap ℤ x (.inl (simpleIndex j))) = 0
  simp only [typeE6RootPairing_base_cartan_apply, ambientMap_cartan, Int.cast_id]
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  rw [cartanZero_killed i hi, cartanOne_killed i hi, zero_mul, zero_mul, add_zero]

private theorem e_cartan (i j : Base.support) (x : Space ℤ) :
    (eMatrix i *ᵥ x) (.inl j) =
      if j = i then x (.inr (Pairing.reflectionPerm i i)) else 0 := by
  by_cases h : j = i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, eMatrix, h]

private theorem e_root (i : Base.support) (r : typeE6Roots) (x : Space ℤ) :
    (eMatrix i *ᵥ x) (.inr r) =
      (if r = i then ∑ j : Base.support, |Base.cartanMatrix i j| * x (.inl j) else 0) +
      ∑ t : typeE6Roots,
        (if Pairing.root r = Pairing.root i + Pairing.root t then
          (Pairing.chainBotCoeff i t : ℤ) + 1 else 0) * x (.inr t) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, eMatrix,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  apply congrArg₂ (· + ·)
  · by_cases h : r = i <;> simp [h]
  · apply Finset.sum_congr rfl
    intro t ht
    congr 2

private theorem ambientMap_e (i : Fin 6) (hi : i = 2 ∨ i = 3) (x : Space ℤ) :
    eMatrix (simpleIndex i) *ᵥ ambientMap ℤ x =
      ambientMap ℤ (eMatrix (simpleIndex i) *ᵥ x) := by
  have hs := rootSign_fixed (simple_fixed i hi)
  have hn := rootSign_fixed (neg_simple_fixed i hi)
  ext (j | r)
  · obtain ⟨j, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
    rw [e_cartan, ambientMap_root, hn]
    simp only [Int.cast_id, zero_mul, ite_self]
    change 0 = ambientMap ℤ (eMatrix (simpleIndex i) *ᵥ x) (.inl (simpleIndex j))
    rw [ambientMap_cartan]
    simp only [e_cartan, simpleIndex, Equiv.apply_eq_iff_eq]
    rcases hi with rfl | rfl <;> norm_num [Fin.ext_iff]
  · rw [e_root, cartanRow_ambientMap i hi]
    simp only [ite_self, zero_add, ambientMap_root, Int.cast_id, e_root, mul_add]
    have hzero : rootSign r *
        (if r = simpleIndex i then ∑ j : Base.support,
          |Base.cartanMatrix (simpleIndex i) j| * x (.inl j) else 0) = 0 := by
      split_ifs with h
      · rw [h, hs, zero_mul]
      · exact mul_zero _
    rw [hzero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs with h
    · rw [rootSign_add (simple_fixed i hi) h]
      ring
    · ring

private theorem f_cartan (i j : Base.support) (x : Space ℤ) :
    (fMatrix i *ᵥ x) (.inl j) = if j = i then x (.inr i) else 0 := by
  by_cases h : j = i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fMatrix, h]

private theorem f_root (i : Base.support) (r : typeE6Roots) (x : Space ℤ) :
    (fMatrix i *ᵥ x) (.inr r) =
      (if r = Pairing.reflectionPerm i i then
        ∑ j : Base.support, |Base.cartanMatrix i j| * x (.inl j) else 0) +
      ∑ t : typeE6Roots,
        (if Pairing.root r = Pairing.root t - Pairing.root i then
          (Pairing.chainTopCoeff i t : ℤ) + 1 else 0) * x (.inr t) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fMatrix,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
    RootPairing.indexNeg_neg]
  apply congrArg₂ (· + ·)
  · by_cases h : r = Pairing.reflectionPerm i i <;> simp [h]
  · apply Finset.sum_congr rfl
    intro t ht
    congr 2

private theorem ambientMap_f (i : Fin 6) (hi : i = 2 ∨ i = 3) (x : Space ℤ) :
    fMatrix (simpleIndex i) *ᵥ ambientMap ℤ x =
      ambientMap ℤ (fMatrix (simpleIndex i) *ᵥ x) := by
  have hs := rootSign_fixed (simple_fixed i hi)
  have hn := rootSign_fixed (neg_simple_fixed i hi)
  ext (j | r)
  · obtain ⟨j, rfl⟩ := typeE6RootPairing_baseEquiv.surjective j
    rw [f_cartan, ambientMap_root, hs]
    simp only [Int.cast_id, zero_mul, ite_self]
    change 0 = ambientMap ℤ (fMatrix (simpleIndex i) *ᵥ x) (.inl (simpleIndex j))
    rw [ambientMap_cartan]
    simp only [f_cartan, simpleIndex, Equiv.apply_eq_iff_eq]
    rcases hi with rfl | rfl <;> norm_num [Fin.ext_iff]
  · rw [f_root, cartanRow_ambientMap i hi]
    simp only [ite_self, zero_add, ambientMap_root, Int.cast_id, f_root, mul_add]
    have hzero : rootSign r *
        (if r = Pairing.reflectionPerm (simpleIndex i) (simpleIndex i) then
          ∑ j : Base.support, |Base.cartanMatrix (simpleIndex i) j| * x (.inl j) else 0) = 0 := by
      split_ifs with h
      · rw [h, hn, zero_mul]
      · exact mul_zero _
    rw [hzero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs with h
    · rw [rootSign_sub (simple_fixed i hi) h]
      ring
    · ring

/-- Matrix of the same integral sign and Cartan map, in the original coordinates. -/
def ambientMatrix (R : Type*) [CommRing R] : Matrix Index Index R :=
  LinearMap.toMatrix' (ambientMap R)

@[simp] theorem ambientMatrix_mulVec (R : Type*) [CommRing R] (x : Space R) :
    ambientMatrix R *ᵥ x = ambientMap R x :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] theorem map_ambientMatrix {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (ambientMatrix R).map f = ambientMatrix S := by
  ext (i | r) j <;>
    simp [ambientMatrix, LinearMap.toMatrix'_apply, ambientMap, Pi.single_apply, apply_ite f]

/-- Both integral Geck operators commute with the concrete ambient map. -/
theorem operator_commutes (s : Bool) (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) 1 * ambientMatrix ℤ =
      ambientMatrix ℤ * (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) 1 := by
  have h (x : Space ℤ) :
      (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) 1 *ᵥ ambientMap ℤ x =
        ambientMap ℤ ((simpleFamily (b := Base)).dividedPower (s, simpleIndex i) 1 *ᵥ x) := by
    cases s
    · simpa only [simpleFamily, fDividedPower_one] using ambientMap_f i hi x
    · exact ambientMap_e i hi x
  ext a b
  have hh := h (Pi.single b 1)
  rw [← ambientMatrix_mulVec, ← ambientMatrix_mulVec, mulVec_mulVec,
    mulVec_mulVec, mulVec_single_one, mulVec_single_one] at hh
  exact congrFun hh a

private theorem operator_factorial (s : Bool) (i : Fin 6) (k : ℕ) :
    (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) 1 ^ k = k.factorial •
      (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) k := by
  cases s
  · simpa only [simpleFamily, fDividedPower_one] using
      fMatrix_pow_eq_factorial_smul (simpleIndex i) k
  · exact eMatrix_pow_eq_factorial_smul (simpleIndex i) k

/-- Integral factorial cancellation promotes commutation to the complete curve. -/
theorem polynomial_commutes (s : Bool) (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    AdjointRestriction.targetCurve (Polynomial ℤ) s i Polynomial.X *
        ambientMatrix (Polynomial ℤ) =
      ambientMatrix (Polynomial ℤ) * AdjointRestriction.targetCurve (Polynomial ℤ) s i Polynomial.X := by
  simpa only [AdjointRestriction.targetCurve, map_ambientMatrix] using
    IntegralCubicFamily.Intertwining.curve_intertwines
      (simpleFamily (b := Base)) (simpleFamily (b := Base))
      (s, simpleIndex i) (s, simpleIndex i) (ambientMatrix ℤ)
      (operator_factorial s i) (operator_factorial s i) (operator_commutes s i hi)

/-- Scalar extension preserves the unchanged parameter in every characteristic. -/
theorem curve_commutes (R : Type*) [CommRing R]
    (s : Bool) (i : Fin 6) (hi : i = 2 ∨ i = 3) (t : R) :
    AdjointRestriction.targetCurve R s i t * ambientMatrix R =
      ambientMatrix R * AdjointRestriction.targetCurve R s i t := by
  let ev : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have h := congrArg (fun A => Matrix.map A ev) (polynomial_commutes s i hi)
  simp only [Matrix.map_mul, map_ambientMatrix, AdjointRestriction.map_targetCurve] at h
  simpa only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

/-- The concrete injection intertwines both signed long-A2 generators. -/
theorem intertwines (F : Type*) [Field F] : Intertwines F := by
  intro s k t v
  apply Subtype.ext
  change ambientMap F (foldedMatrix F (f4Simple F s (pairNode 0 1 k) t) *ᵥ (v : Space F)) =
    foldedMatrix F (f4Simple F s (pairNode 0 1 k) t) *ᵥ ambientMap F v
  simp only [foldedMatrix, AdjointRestriction.f4Simple_matrix]
  rw [← ambientMatrix_mulVec, ← ambientMatrix_mulVec, mulVec_mulVec, mulVec_mulVec]
  congr 1
  cases k
  · exact (curve_commutes F s 2 (Or.inl rfl) t).symm
  · exact (curve_commutes F s 3 (Or.inr rfl) t).symm

/-- Actual application to all words, with the original pair inclusion and actions. -/
theorem word_intertwines_unconditionally (F : Type*) [Field F]
    (w : PairWord F) (v : complementSpace F) :
    toFixed F (wordAction F (-1) w v) = wordAction F 1 w (toFixed F v) :=
  word_intertwines F (intertwines F) w v

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
