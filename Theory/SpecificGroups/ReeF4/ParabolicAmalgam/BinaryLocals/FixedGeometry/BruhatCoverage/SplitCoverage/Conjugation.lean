module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.RootConditions
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves

/-!
# Simple Weyl conjugation for the binary split F4 matrices

For a positive root other than the reflecting simple root, prepend that simple
reflection to its canonical route. The existing characteristic-two route
comparison identifies the resulting curve with the canonical reflected curve.
Use the same route for negative roots. On the reflecting root itself, specialize
the integral rank-one identities `titsLift_mul_eUnipotent` and
`titsLift_mul_fUnipotent`. Every binary parameter is zero or one.

This proves GLS3 1.12.1(h) for the actual matrices used here, without a BN-pair
or Bruhat assumption. Source: `refs/KGroup/GLS3/Chapter1.tex` and the integral
Chevalley construction in Steinberg, *Lectures on Chevalley Groups*.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup WordRelations
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem titsUnit_simple_mul_positive (i : typeF4RootPairing_base.support) :
    titsUnit [i] * F4Chevalley.rootCurve i.val (1 : CoefficientField 0) =
      F4Chevalley.rootCurve (-i.val) 1 * titsUnit [i] := by
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators i.val _ =
    rootCurveUnit integralChevalleyRootOperators (-i.val) _ * titsUnit [i]
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * positiveMatrix i 1 =
    negativeMatrix i 1 * specializeMatrix (titsWord [i])
  simp only [titsWord, mul_one]
  have he := congrArg (specializeMatrix (S := CoefficientField 0))
    (titsLift_mul_eUnipotent i 1)
  rw [specializeMatrix_mul, specializeMatrix_mul] at he
  simpa only [specializeMatrix,
    Faithfulness.Adjoint.map_eUnipotent, Faithfulness.Adjoint.map_fUnipotent,
    Int.cast_one, Int.cast_neg, CharTwo.neg_eq] using he

private theorem titsUnit_simple_mul_negative (i : typeF4RootPairing_base.support) :
    titsUnit [i] * F4Chevalley.rootCurve (-i.val) (1 : CoefficientField 0) =
      F4Chevalley.rootCurve i.val 1 * titsUnit [i] := by
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators (-i.val) _ =
    rootCurveUnit integralChevalleyRootOperators i.val _ * titsUnit [i]
  rw [rootCurveUnit_neg_simple, rootCurveUnit_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * negativeMatrix i 1 =
    positiveMatrix i 1 * specializeMatrix (titsWord [i])
  simp only [titsWord, mul_one]
  have he := congrArg (specializeMatrix (S := CoefficientField 0))
    (titsLift_mul_fUnipotent i 1)
  rw [specializeMatrix_mul, specializeMatrix_mul] at he
  simpa only [specializeMatrix,
    Faithfulness.Adjoint.map_eUnipotent, Faithfulness.Adjoint.map_fUnipotent,
    Int.cast_one, Int.cast_neg, CharTwo.neg_eq] using he

private theorem titsUnit_single_mul (i : typeF4RootPairing_base.support)
    (w : List typeF4RootPairing_base.support) :
    titsUnit (S := CoefficientField 0) [i] * titsUnit w = titsUnit (i :: w) := by
  rw [titsUnit_cons, titsUnit_cons, titsUnit_nil, mul_one]

private theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) = -typeF4RootPairing.reflectionPerm i r := by
  apply typeF4RootPairing.root.injective
  have hrootneg (q : F4Chevalley.Root) :
      typeF4RootPairing.root (-q) = -typeF4RootPairing.root q := by
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  simp only [hrootneg, RootPairing.root_reflectionPerm, map_neg]

private theorem titsUnit_conj_positive (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
    titsUnit [i] * F4Chevalley.rootCurve r (1 : CoefficientField 0) * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val r) 1 := by
  by_cases hi : r = i.val
  · subst r
    change _ = F4Chevalley.rootCurve (-i.val) 1
    rw [titsUnit_simple_mul_positive]
    group
  · have hp := hr.reflectionPerm i.property hi
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    have htarget : reflectionWord (P := typeF4RootPairing) (i :: D.word) D.simple =
        typeF4RootPairing.reflectionPerm i.val r := by
      change typeF4RootPairing.reflectionPerm i.val (reflectionWord D.word D.simple) = _
      rw [D.target]
    rw [rootCurve_of_pos_route r hr,
      rootCurve_of_pos_transport _ hp (i :: D.word) D.simple htarget]
    change titsUnit [i] * (titsUnit D.word * F4Chevalley.rootCurve D.simple.val 1 *
        (titsUnit D.word)⁻¹) * (titsUnit [i])⁻¹ = _
    rw [← titsUnit_single_mul i D.word]
    group

private theorem titsUnit_conj_negative (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
    titsUnit [i] * F4Chevalley.rootCurve (-r) (1 : CoefficientField 0) * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val (-r)) 1 := by
  by_cases hi : r = i.val
  · subst r
    rw [reflection_neg]
    change _ = F4Chevalley.rootCurve (-(-i.val)) 1
    rw [neg_neg, titsUnit_simple_mul_negative]
    group
  · have hp := hr.reflectionPerm i.property hi
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    have htarget : reflectionWord (P := typeF4RootPairing) (i :: D.word) D.simple =
        typeF4RootPairing.reflectionPerm i.val r := by
      change typeF4RootPairing.reflectionPerm i.val (reflectionWord D.word D.simple) = _
      rw [D.target]
    rw [reflection_neg, rootCurve_neg_of_pos_route r hr,
      rootCurve_neg_of_pos_transport _ hp (i :: D.word) D.simple htarget]
    change titsUnit [i] * (titsUnit D.word * F4Chevalley.rootCurve (-D.simple.val) 1 *
        (titsUnit D.word)⁻¹) * (titsUnit [i])⁻¹ = _
    rw [← titsUnit_single_mul i D.word]
    group

/-- Simple Weyl conjugation on the actual binary root matrices, with no
geometric certificate or factorization assumption. -/
theorem binarySimpleRootConjugation : BinarySimpleRootConjugation := by
  intro i r t
  have ht : t = 0 ∨ t = 1 := by
    apply eq_zero_or_one_of_sq_eq_self
    simpa using field_pow 0 t
  apply Subtype.ext
  rcases ht with rfl | rfl
  · change _ * F4Chevalley.rootCurve r 0 * _ = F4Chevalley.rootCurve _ 0
    rw [F4Chevalley.rootCurve_zero, F4Chevalley.rootCurve_zero]
    simp
  · have hw : (simpleWord 0 [i] : MatrixUnits 0) =
        titsUnit [typeF4RootPairing_baseEquiv i] := by
      rw [simpleWord_coe]
      rfl
    change (simpleWord 0 [i] : MatrixUnits 0) * F4Chevalley.rootCurve r 1 *
      (simpleWord 0 [i] : MatrixUnits 0)⁻¹ = F4Chevalley.rootCurve _ 1
    rw [hw]
    by_cases hr : typeF4RootPairing_base.IsPos r
    · exact titsUnit_conj_positive (typeF4RootPairing_baseEquiv i) r hr
    · have hp := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
      simpa only [neg_neg, typeF4RootPairing_baseEquiv_val] using titsUnit_conj_negative (typeF4RootPairing_baseEquiv i) (-r) hp

end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
