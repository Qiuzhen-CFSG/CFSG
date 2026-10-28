module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.RootConditions
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Simple reflection on the full split F₄ root curves

A simple Tits lift conjugates each root curve to its reflected curve in
characteristic two. For the reflecting root, extract the three coefficients
from the integral rank-one identities at parameters 1, -1, and 2, then
specialize to the coefficient field. For the other roots, prepend the
reflection to the chosen route and apply the proved route comparison.

This extends the binary argument in
`ParabolicAmalgam/BinaryLocals/FixedGeometry/BruhatCoverage/SplitCoverage/Conjugation`
to arbitrary parameters; it uses no field-size dichotomy. Source: GLS3
1.12.1(h), `refs/KGroup/GLS3/Chapter1.tex`, and the integral Chevalley
construction in Steinberg, *Lectures on Chevalley Groups*.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup WordRelations
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem titsUnit_simple_mul_positive (m : ℕ)
    (i : typeF4RootPairing_base.support) (t : CoefficientField m) :
    titsUnit [i] * F4Chevalley.rootCurve i.val t =
      F4Chevalley.rootCurve (-i.val) t * titsUnit [i] := by
  have hc (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
      titsLift i * eDividedPower i k =
        (-1 : ℤ) ^ k • (fDividedPower i k * titsLift i) := by
    ext x y
    have h1 := congrFun (congrFun (titsLift_mul_eUnipotent i 1) x) y
    have hm1 := congrFun (congrFun (titsLift_mul_eUnipotent i (-1)) x) y
    have h2 := congrFun (congrFun (titsLift_mul_eUnipotent i 2) x) y
    simp only [eUnipotent, fUnipotent, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 hm1 h2
    rcases hk with rfl | rfl | rfl <;>
      simp only [Matrix.smul_apply, smul_eq_mul] <;> norm_num at * <;> omega
  have hs (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
      specializeMatrix (S := CoefficientField m) (titsLift i) *
        specializeMatrix (eDividedPower i k) =
      specializeMatrix (fDividedPower i k) * specializeMatrix (titsLift i) := by
    rw [← specializeMatrix_mul, ← specializeMatrix_mul, hc k hk]
    ext x y
    change (((-1 : ℤ) ^ k * _ : ℤ) : CoefficientField m) = _
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      CharTwo.neg_eq, one_pow, one_mul]
    rfl
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators i.val _ =
    rootCurveUnit integralChevalleyRootOperators (-i.val) _ * titsUnit [i]
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * positiveMatrix i t =
    negativeMatrix i t * specializeMatrix (titsWord [i])
  simp only [titsWord, mul_one, positiveMatrix_formula, negativeMatrix_formula,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [specializeMatrix] at hs ⊢
  rw [hs 1 (by simp), hs 2 (by simp), hs 3 (by simp)]

private theorem titsUnit_simple_mul_negative (m : ℕ)
    (i : typeF4RootPairing_base.support) (t : CoefficientField m) :
    titsUnit [i] * F4Chevalley.rootCurve (-i.val) t =
      F4Chevalley.rootCurve i.val t * titsUnit [i] := by
  have hc (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
      titsLift i * fDividedPower i k =
        (-1 : ℤ) ^ k • (eDividedPower i k * titsLift i) := by
    ext x y
    have h1 := congrFun (congrFun (titsLift_mul_fUnipotent i 1) x) y
    have hm1 := congrFun (congrFun (titsLift_mul_fUnipotent i (-1)) x) y
    have h2 := congrFun (congrFun (titsLift_mul_fUnipotent i 2) x) y
    simp only [fUnipotent, eUnipotent, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1 hm1 h2
    rcases hk with rfl | rfl | rfl <;>
      simp only [Matrix.smul_apply, smul_eq_mul] <;> norm_num at * <;> omega
  have hs (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
      specializeMatrix (S := CoefficientField m) (titsLift i) *
        specializeMatrix (fDividedPower i k) =
      specializeMatrix (eDividedPower i k) * specializeMatrix (titsLift i) := by
    rw [← specializeMatrix_mul, ← specializeMatrix_mul, hc k hk]
    ext x y
    change (((-1 : ℤ) ^ k * _ : ℤ) : CoefficientField m) = _
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      CharTwo.neg_eq, one_pow, one_mul]
    rfl
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators (-i.val) _ =
    rootCurveUnit integralChevalleyRootOperators i.val _ * titsUnit [i]
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * negativeMatrix i t =
    positiveMatrix i t * specializeMatrix (titsWord [i])
  simp only [titsWord, mul_one, positiveMatrix_formula, negativeMatrix_formula,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp only [specializeMatrix] at hs ⊢
  rw [hs 1 (by simp), hs 2 (by simp), hs 3 (by simp)]

private theorem titsUnit_single_mul (m : ℕ) (i : typeF4RootPairing_base.support)
    (w : List typeF4RootPairing_base.support) :
    titsUnit (S := CoefficientField m) [i] * titsUnit w = titsUnit (i :: w) := by
  rw [titsUnit_cons, titsUnit_cons, titsUnit_nil, mul_one]

private theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) = -typeF4RootPairing.reflectionPerm i r := by
  apply typeF4RootPairing.root.injective
  have hrootneg (q : F4Chevalley.Root) :
      typeF4RootPairing.root (-q) = -typeF4RootPairing.root q := by
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  simp only [hrootneg, RootPairing.root_reflectionPerm, map_neg]

private theorem titsUnit_conj_positive (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    titsUnit [i] * F4Chevalley.rootCurve r (t : CoefficientField m) * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val r) t := by
  by_cases hi : r = i.val
  · subst r
    change _ = F4Chevalley.rootCurve (-i.val) t
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
    change titsUnit [i] * (titsUnit D.word * F4Chevalley.rootCurve D.simple.val t *
        (titsUnit D.word)⁻¹) * (titsUnit [i])⁻¹ = _
    rw [← titsUnit_single_mul m i D.word]
    group

private theorem titsUnit_conj_negative (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    titsUnit [i] * F4Chevalley.rootCurve (-r) (t : CoefficientField m) * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val (-r)) t := by
  by_cases hi : r = i.val
  · subst r
    rw [reflection_neg]
    change _ = F4Chevalley.rootCurve (-(-i.val)) t
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
    change titsUnit [i] * (titsUnit D.word * F4Chevalley.rootCurve (-D.simple.val) t *
        (titsUnit D.word)⁻¹) * (titsUnit [i])⁻¹ = _
    rw [← titsUnit_single_mul m i D.word]
    group


/-- Simple reflection conjugation over the full coefficient field. -/
theorem rankOneRepresentative_one_conj_root (m : ℕ) (i : Fin 4)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    rankOneRepresentative m (typeF4SimpleRootIndex i) 1 * rootGeneratorInGroup m r t *
      (rankOneRepresentative m (typeF4SimpleRootIndex i) 1)⁻¹ =
      rootGeneratorInGroup m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
  apply Subtype.ext
  have hw : (rankOneRepresentative m (typeF4SimpleRootIndex i) 1 : MatrixUnits m) =
      titsUnit [typeF4RootPairing_baseEquiv i] := by
    simp [rankOneRepresentative, titsUnit_cons, titsUnit_nil,
      typeF4RootPairing_baseEquiv_val]
  change (rankOneRepresentative m (typeF4SimpleRootIndex i) 1 : MatrixUnits m) *
    F4Chevalley.rootCurve r t *
    (rankOneRepresentative m (typeF4SimpleRootIndex i) 1 : MatrixUnits m)⁻¹ =
    F4Chevalley.rootCurve
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t
  rw [hw]
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact titsUnit_conj_positive m (typeF4RootPairing_baseEquiv i) r hr t
  · have hp := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    simpa only [neg_neg, typeF4RootPairing_baseEquiv_val] using
      titsUnit_conj_negative m (typeF4RootPairing_baseEquiv i) (-r) hp t

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
