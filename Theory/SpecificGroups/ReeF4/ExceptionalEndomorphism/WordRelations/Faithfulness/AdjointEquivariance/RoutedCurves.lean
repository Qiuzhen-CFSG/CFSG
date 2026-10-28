module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.Transport
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# Transport from simple curves to the actual routed F4 curves

The specialized integral Tits word is a product of the positive and negative
simple polynomial curves. Each canonical F4 root curve is its conjugate of a
simple curve, along exactly the route chosen in `IntegralAllRootOperators`.
Thus adjoint equivariance for both simple directions implies equivariance for
every actual root curve. No comparison between distinct root routes is used.

The transport calculations expand the integral divided-power exponential, as
in `IntegralChevalleyRootCurves`. The Tits convention is
`x_i(1) y_i(-1) x_i(1)`, following Geck's integral construction and Steinberg's
*Lectures on Chevalley Groups*. Everything here holds over any commutative ring.
-/

@[expose] public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint
noncomputable section
variable {K : Type*} [CommRing K]

/-- The Tits unit is a word in the actual simple polynomial curves. -/
def titsUnit (i : typeF4RootPairing_base.support) :
    (Matrix Coordinate Coordinate K)ˣ :=
  positiveUnit i 1 * negativeUnit i (-1) * positiveUnit i 1

lemma map_eUnipotent (i : typeF4RootPairing_base.support) (t : ℤ) :
    (eUnipotent (P := typeF4RootPairing) i t).map (Int.castRingHom K) =
      positiveMatrix i (t : K) := by
  ext x y
  simp only [eUnipotent, positiveMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma map_fUnipotent (i : typeF4RootPairing_base.support) (t : ℤ) :
    (fUnipotent (P := typeF4RootPairing) i t).map (Int.castRingHom K) =
      negativeMatrix i (t : K) := by
  ext x y
  simp only [fUnipotent, negativeMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma titsUnit_val (i : typeF4RootPairing_base.support) :
    (titsUnit (K := K) i : Matrix Coordinate Coordinate K) =
      (titsLift (P := typeF4RootPairing) i).map (Int.castRingHom K) := by
  change positiveMatrix i 1 * negativeMatrix i (-1) * positiveMatrix i 1 = _
  rw [titsLift, Matrix.map_mul, Matrix.map_mul, map_eUnipotent, map_fUnipotent]
  simp

/-- A word of integral Tits lifts, regarded as matrix units after specialization. -/
def titsWordUnit : List typeF4RootPairing_base.support →
    (Matrix Coordinate Coordinate K)ˣ
  | [] => 1
  | i :: w => titsUnit i * titsWordUnit w

lemma titsWordUnit_val (w : List typeF4RootPairing_base.support) :
    (titsWordUnit (K := K) w : Matrix Coordinate Coordinate K) =
      (titsWord (P := typeF4RootPairing) w).map (Int.castRingHom K) := by
  induction w with
  | nil => simp [titsWordUnit, titsWord]
  | cons i w ih =>
      change (titsUnit (K := K) i : Matrix Coordinate Coordinate K) * (titsWordUnit (K := K) w : Matrix Coordinate Coordinate K) = _
      rw [titsUnit_val, ih, titsWord, Matrix.map_mul]

lemma titsWordUnit_inv_val (w : List typeF4RootPairing_base.support) :
    (↑(titsWordUnit (K := K) w)⁻¹ : Matrix Coordinate Coordinate K) =
      (titsWordInv (P := typeF4RootPairing) w).map (Int.castRingHom K) := by
  apply (Units.mul_left_inj (titsWordUnit (K := K) w)).mp
  rw [Units.inv_mul, titsWordUnit_val, ← Matrix.map_mul, titsWord_inv_mul]
  simp

lemma rootCurve_pos_transport (r : typeF4Roots)
    (hr : typeF4RootPairing_base.IsPos r) (t : K) :
    F4Chevalley.rootCurve r t =
      titsWordUnit (rootRoute (P := typeF4RootPairing) r).word *
        positiveUnit (rootRoute (P := typeF4RootPairing) r).simple t *
        (titsWordUnit (rootRoute (P := typeF4RootPairing) r).word)⁻¹ := by
  apply Units.ext
  change rootCurveMatrix (integralChevalleyRootOperators (P := typeF4RootPairing)) r t = _
  change 1 + t • specializeMatrix (rootDividedPower (P := typeF4RootPairing) r 1) +
    t ^ 2 • specializeMatrix (rootDividedPower (P := typeF4RootPairing) r 2) +
    t ^ 3 • specializeMatrix (rootDividedPower (P := typeF4RootPairing) r 3) = _
  simp only [rootDividedPower_of_pos r hr, specializeMatrix_transportedMatrix,
    Units.val_mul, titsWordUnit_val, titsWordUnit_inv_val, positiveUnit_val,
    positiveMatrix_formula]
  have hTU := Units.mul_inv (titsWordUnit (K := K)
    (rootRoute (P := typeF4RootPairing) r).word)
  simp only [titsWordUnit_val, titsWordUnit_inv_val] at hTU
  simp only [specializeMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  noncomm_ring [hTU]

lemma rootCurve_neg_transport (r : typeF4Roots)
    (hr : typeF4RootPairing_base.IsPos r) (t : K) :
    let _ := typeF4RootPairing.indexNeg
    F4Chevalley.rootCurve (-r) t =
      titsWordUnit (rootRoute (P := typeF4RootPairing) r).word *
        negativeUnit (rootRoute (P := typeF4RootPairing) r).simple t *
        (titsWordUnit (rootRoute (P := typeF4RootPairing) r).word)⁻¹ := by
  let _ := typeF4RootPairing.indexNeg
  apply Units.ext
  change rootCurveMatrix (integralChevalleyRootOperators (P := typeF4RootPairing)) (-r) t = _
  change 1 + t • specializeMatrix (rootDividedPower (P := typeF4RootPairing) (-r) 1) +
    t ^ 2 • specializeMatrix (rootDividedPower (P := typeF4RootPairing) (-r) 2) +
    t ^ 3 • specializeMatrix (rootDividedPower (P := typeF4RootPairing) (-r) 3) = _
  simp only [rootDividedPower_neg_of_pos r hr, specializeMatrix_transportedMatrix,
    Units.val_mul, titsWordUnit_val, titsWordUnit_inv_val, negativeUnit_val,
    negativeMatrix_formula]
  have hTU := Units.mul_inv (titsWordUnit (K := K)
    (rootRoute (P := typeF4RootPairing) r).word)
  simp only [titsWordUnit_val, titsWordUnit_inv_val] at hTU
  simp only [specializeMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  noncomm_ring [hTU]

/-- The canonical positive-simple route is empty. -/
theorem rootCurve_simple (i : typeF4RootPairing_base.support) (t : K) :
    F4Chevalley.rootCurve i t = positiveUnit i t := by
  rw [rootCurve_pos_transport i (typeF4RootPairing_base.isPos_of_mem_support i.property)]
  simp [titsWordUnit]

/-- The negative-simple curve uses the same empty positive route. -/
theorem rootCurve_neg_simple (i : typeF4RootPairing_base.support) (t : K) :
    letI := typeF4RootPairing.indexNeg
    F4Chevalley.rootCurve (-(i : typeF4Roots)) t = negativeUnit i t := by
  let _ := typeF4RootPairing.indexNeg
  rw [rootCurve_neg_transport i (typeF4RootPairing_base.isPos_of_mem_support i.property)]
  simp [titsWordUnit]

lemma titsWordUnit_equivariant (D : (Coordinate → K) → Matrix Coordinate Coordinate K)
    (he : ∀ (i : typeF4RootPairing_base.support) (t : K), Equivariant D (positiveUnit i t))
    (hf : ∀ (i : typeF4RootPairing_base.support) (t : K), Equivariant D (negativeUnit i t))
    (w : List typeF4RootPairing_base.support) : Equivariant D (titsWordUnit w) := by
  induction w with
  | nil => intro v; simp [titsWordUnit]
  | cons i w ih =>
    exact equivariant_mul D _ _
      (equivariant_mul D _ _ (equivariant_mul D _ _ (he i 1) (hf i (-1))) (he i 1)) ih

/-- Every actual routed F4 curve is equivariant if both simple directions are. -/
theorem rootCurve_equivariant_of_simple
    (D : (Coordinate → K) → Matrix Coordinate Coordinate K)
    (he : ∀ (i : typeF4RootPairing_base.support) (t : K), Equivariant D (positiveUnit i t))
    (hf : ∀ (i : typeF4RootPairing_base.support) (t : K), Equivariant D (negativeUnit i t))
    (r : typeF4Roots) (t : K) : Equivariant D (F4Chevalley.rootCurve r t) := by
  let _ := typeF4RootPairing.indexNeg
  by_cases hr : typeF4RootPairing_base.IsPos r
  · rw [rootCurve_pos_transport r hr]
    exact equivariant_conjugate D _ _ (titsWordUnit_equivariant D he hf _) (he _ t)
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have h := rootCurve_neg_transport (-r) hn t
    simp only [neg_neg] at h
    rw [h]
    exact equivariant_conjugate D _ _ (titsWordUnit_equivariant D he hf _) (hf _ t)
end
end ReeF4.WordRelations.Faithfulness.Adjoint
