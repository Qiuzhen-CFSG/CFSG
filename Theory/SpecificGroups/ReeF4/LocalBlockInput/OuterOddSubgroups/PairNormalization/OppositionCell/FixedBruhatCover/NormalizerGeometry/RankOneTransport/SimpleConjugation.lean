module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Simple F4 reflections on all root parameters

A simple Tits lift conjugates every root curve to its reflected curve over any
commutative ring of characteristic two. For the opposite simple roots, first
transport the integral divided powers using the signed infinitesimal identity;
its factorials are cancelled over the integers before specialization. For the
other roots, prepend the simple reflection to the canonical positive route and
use the characteristic-two route comparison. Negative roots use the same route.

This extends the binary calculation in `SplitCoverage.Conjugation` to arbitrary
parameters without changing that module. Source: GLS3 1.12.1(h),
`refs/KGroup/GLS3/Chapter1.tex`, and the integral construction in Steinberg,
*Lectures on Chevalley Groups*.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open scoped Matrix
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
variable {S : Type*} [CommRing S] [CharP S 2]

private theorem simple_dividedPower_conj (i : typeF4RootPairing_base.support) (n : ℕ) :
    specializeMatrix (S := S) (transportedMatrix [i] (eDividedPower i n)) =
      specializeMatrix (fDividedPower i n) := by
  apply RouteComparison.map_eq_of_sign_smul _ _ (-1) n (by norm_num)
  apply RouteComparison.dividedPower_eq_sign_smul
    (transportedMatrix [i] (eMatrix i)) (fMatrix i) _ _ n (-1)
  · rw [← transportedMatrix_pow, eMatrix_pow_eq_factorial_smul, transportedMatrix_smul]
  · exact fMatrix_pow_eq_factorial_smul i n
  · simpa only [transportedMatrix, titsWord, titsWordInv_cons, titsWordInv_nil,
      mul_one, one_mul, neg_one_smul] using RouteComparison.titsLift_conj_eMatrix_neg i

private theorem simple_positive_conj (i : typeF4RootPairing_base.support) (t : S) :
    titsUnit [i] * F4Chevalley.rootCurve i.val t * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (-i.val) t := by
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators i.val t * _ =
    rootCurveUnit integralChevalleyRootOperators (-i.val) t
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * RootPairing.SimpleGeckGroup.positiveMatrix i t *
    specializeMatrix (titsWordInv [i]) = RootPairing.SimpleGeckGroup.negativeMatrix i t
  have hTI : specializeMatrix (S := S) (titsWord [i]) *
      specializeMatrix (titsWordInv [i]) = 1 := (titsUnit (S := S) [i]).val_inv
  have h (n : ℕ) : specializeMatrix (titsWord [i]) *
      (eDividedPower i n).map (Int.castRingHom S) * specializeMatrix (titsWordInv [i]) =
      (fDividedPower i n).map (Int.castRingHom S) := by
    change specializeMatrix (titsWord [i]) * specializeMatrix (eDividedPower i n) *
      specializeMatrix (titsWordInv [i]) = specializeMatrix (fDividedPower i n)
    rw [← specializeMatrix_transportedMatrix]
    exact simple_dividedPower_conj i n
  simp only [RootPairing.SimpleGeckGroup.positiveMatrix_formula,
    RootPairing.SimpleGeckGroup.negativeMatrix_formula,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hTI, h, h, h]

private theorem simple_inv (i : typeF4RootPairing_base.support) :
    (titsUnit (S := S) [i])⁻¹ = titsUnit [i] := by
  rw [titsUnit_cons, titsUnit_nil, mul_one]
  simp only [mul_inv_rev, F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  group

private theorem simple_negative_conj (i : typeF4RootPairing_base.support) (t : S) :
    titsUnit [i] * F4Chevalley.rootCurve (-i.val) t * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve i.val t := by
  calc
    _ = (titsUnit [i])⁻¹ * F4Chevalley.rootCurve (-i.val) t * titsUnit [i] := by
      rw [simple_inv]
    _ = _ := by rw [← simple_positive_conj i t]; group

omit [CharP S 2] in
private theorem titsUnit_single_mul (i : typeF4RootPairing_base.support)
    (w : List typeF4RootPairing_base.support) :
    titsUnit (S := S) [i] * titsUnit w = titsUnit (i :: w) := by
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
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    titsUnit [i] * F4Chevalley.rootCurve r t * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val r) t := by
  by_cases hi : r = i.val
  · subst r
    exact simple_positive_conj i t
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
    rw [← titsUnit_single_mul i D.word]
    group

private theorem titsUnit_conj_negative (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : S) :
    titsUnit [i] * F4Chevalley.rootCurve (-r) t * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val (-r)) t := by
  by_cases hi : r = i.val
  · subst r
    rw [reflection_neg]
    change _ = F4Chevalley.rootCurve (-(-i.val)) t
    rw [neg_neg]
    exact simple_negative_conj i t
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
    rw [← titsUnit_single_mul i D.word]
    group

/-- Simple Tits conjugation reflects every F4 root, for every parameter in a
commutative ring of characteristic two. -/
theorem simple_conj (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (t : S) :
    titsUnit [i] * F4Chevalley.rootCurve r t * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (typeF4RootPairing.reflectionPerm i.val r) t := by
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact titsUnit_conj_positive i r hr t
  · have hp := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    simpa only [neg_neg] using titsUnit_conj_negative i (-r) hp t

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
