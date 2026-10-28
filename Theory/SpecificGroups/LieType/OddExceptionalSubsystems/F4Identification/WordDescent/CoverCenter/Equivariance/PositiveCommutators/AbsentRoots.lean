module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.IntegralModel
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums

/-!
# Absent-root commutators for the signed integral F4 operators

The integral absent-weight theorem kills the positive-simple commutator.
For a negative root, append the source simple reflection to the canonical
route and use its exact negative lowering operator. Multiplication by the
fixed root orientation then preserves the zero commutator. This proves the
absent-root branch of `PositiveCommutators` without any characteristic-two
specialization.

Sources: `IntegralAllRootOperators`, the integral absent-weight proof in
`PositiveSimple.RootLinear.NoRootSums`, and the GLS3 §§2.2–2.6 conventions.
-/

public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

/-- The signed integral operators commute at an absent nonzero root sum. -/
lemma integral_root_commutator_zero (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hopp : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hsum : typeF4RootPairing.root i + typeF4RootPairing.root r ∉
      Set.range typeF4RootPairing.root) :
    eMatrix (P := typeF4RootPairing) i * integralCoordinateOperator (Sum.inr r) -
      integralCoordinateOperator (Sum.inr r) * eMatrix i = 0 := by
  let := typeF4RootPairing.indexNeg
  have h0 : typeF4RootPairing.root i + typeF4RootPairing.root r ≠ 0 := by
    intro h
    apply hopp
    apply typeF4RootPairing.root.injective
    simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self] using eq_neg_of_add_eq_zero_right h
  suffices he : eMatrix (P := typeF4RootPairing) i *
        rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r -
      rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r * eMatrix i = 0 by
    simp only [integralCoordinateOperator, Matrix.mul_smul, Matrix.smul_mul,
      ← smul_sub, he, smul_zero]
  by_cases hr : typeF4RootPairing_base.IsPos r
  · let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    rw [rootOperator_of_pos r hr]
    exact integral_commutator_zero (P := typeF4RootPairing) i z.simple z.word
      (by simpa only [z.target] using h0) (by simpa only [z.target] using hsum)
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) hn
    simp only [neg_neg] at he
    rw [he]
    let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    have hz : reflectionWord (P := typeF4RootPairing) (z.word ++ [z.simple]) z.simple = r := by
      rw [ReeF4.WordRelations.RouteComparison.reflectionWord_append_simple_self,
        z.target, neg_neg]
    have hc := integral_commutator_zero (P := typeF4RootPairing) i z.simple
      (z.word ++ [z.simple]) (by simpa only [hz] using h0) (by simpa only [hz] using hsum)
    change eMatrix (P := typeF4RootPairing) i * transportedMatrix _ _ -
      transportedMatrix _ _ * eMatrix i = 0 at hc
    rw [ReeF4.WordRelations.RouteComparison.transportedMatrix_append_simple_eMatrix] at hc
    simp only [mul_neg, neg_mul, neg_sub_neg, sub_eq_zero] at hc
    exact sub_eq_zero.mpr hc.symm

/-- Infinitesimal intertwining on root coordinates with absent nonzero sum. -/
lemma positive_integral_commutator_no_root (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hopp : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hsum : typeF4RootPairing.root i + typeF4RootPairing.root r ∉
      Set.range typeF4RootPairing.root) :
    integralAdjointMap (eMatrix (P := typeF4RootPairing) i *ᵥ v (b := typeF4RootPairing_base) r) =
      eMatrix i * integralCoordinateOperator (Sum.inr r) -
        integralCoordinateOperator (Sum.inr r) * eMatrix i := by
  rw [eMatrix_mulVec_v_zero hopp hsum, map_zero, integral_root_commutator_zero i r hopp hsum]

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
