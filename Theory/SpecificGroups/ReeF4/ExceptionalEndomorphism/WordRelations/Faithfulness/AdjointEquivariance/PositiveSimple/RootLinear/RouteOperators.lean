module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison

/-!
# Arbitrary Weyl routes for the actual F4 coordinate operators

Any word carrying a simple root to a given root gives the fixed coordinate
operator after specialization to characteristic two. For a negative endpoint,
append the source simple reflection to its positive opposite's canonical
route; integral conjugation exchanges `e_i` with `-f_i`, and the sign
vanishes after specialization. Concatenating words then proves Weyl
covariance of every actual root coordinate operator.

This supplies a comparison for explicit-route calculations, including negative
roots, without assuming adjoint equivariance. It uses the integral route
comparison from `Intertwining.Transport.RouteComparison`, based on Geck's
construction and the Tits action in `IntegralAllRootOperators`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- Every positive-source route gives the actual operator at its endpoint,
including a negative endpoint. -/
lemma coordinateOperator_eq_transport (m : ℕ) (r : typeF4Roots)
    (w : List typeF4RootPairing_base.support) (j : typeF4RootPairing_base.support)
    (hw : reflectionWord (P := typeF4RootPairing) w j = r) :
    coordinateOperator m (Sum.inr r) =
      (transportedMatrix w (eMatrix (P := typeF4RootPairing) j)).map
        (Int.castRingHom (CoefficientField m)) := by
  let := typeF4RootPairing.indexNeg
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map _ = _
  by_cases hr : typeF4RootPairing_base.IsPos r
  · rw [rootOperator_of_pos r hr]
    have h := RouteComparison.specialize_transported_eDividedPower_eq
      (S := CoefficientField m)
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word w
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple j 1
      ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target.trans hw.symm)
    simpa only [eDividedPower_one, specializeMatrix] using h
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) hn
    simp only [neg_neg] at he
    rw [he]
    let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    have hz : reflectionWord (P := typeF4RootPairing) (z.word ++ [z.simple]) z.simple =
        reflectionWord w j := by
      rw [RouteComparison.reflectionWord_append_simple_self, z.target, neg_neg, hw]
    have h := RouteComparison.specialize_transported_eDividedPower_eq
      (S := CoefficientField m) (z.word ++ [z.simple]) w z.simple j 1 hz
    simp only [eDividedPower_one, RouteComparison.transportedMatrix_append_simple_eMatrix] at h
    ext x y
    have hxy := congrFun (congrFun h x) y
    simpa only [specializeMatrix, Matrix.map_apply, Matrix.neg_apply, map_neg,
      CharTwo.neg_eq] using hxy

private lemma reflectionWord_append (w z : List typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    reflectionWord (P := typeF4RootPairing) (w ++ z) r =
      reflectionWord w (reflectionWord z r) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, reflectionWord, ih]

private lemma titsWordInv_append (w z : List typeF4RootPairing_base.support) :
    titsWordInv (P := typeF4RootPairing) (w ++ z) = titsWordInv z * titsWordInv w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, mul_assoc]

/-- Weyl conjugation carries the actual root operator to the actual operator
at the reflected root. -/
lemma coordinateOperator_reflectionWord (m : ℕ)
    (w : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    coordinateOperator m (Sum.inr (reflectionWord (P := typeF4RootPairing) w r)) =
      (titsWord (P := typeF4RootPairing) w).map (Int.castRingHom (CoefficientField m)) *
        coordinateOperator m (Sum.inr r) *
          (titsWordInv (P := typeF4RootPairing) w).map (Int.castRingHom (CoefficientField m)) := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hwz : reflectionWord (P := typeF4RootPairing) (w ++ z.word) z.simple =
      reflectionWord w r := by rw [reflectionWord_append, z.target]
  rw [coordinateOperator_eq_transport m _ (w ++ z.word) z.simple hwz,
    coordinateOperator_eq_transport m r z.word z.simple z.target]
  simp only [transportedMatrix, titsWord_append, titsWordInv_append,
    Matrix.map_mul, mul_assoc]
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
