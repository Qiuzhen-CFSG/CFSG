module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RouteOperators
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums.AbsentWeights

/-!
# Positive-simple operator commutators with absent root sums

The commutator of two integral Geck root operators has their sum as its Cartan
weight. Extend the root lattice to an algebraic closure of the rationals: the
weight is still nonzero and absent, so `weight_zero_of_absent` makes the
commutator vanish in Geck's Lie algebra. Injectivity of the integer embedding
descends the operator identity to the integral matrices.

For F4, the proved arbitrary-route comparison identifies any positive-source
Tits transport with the actual coordinate operator after specialization,
including negative endpoints. Thus the integral identity proves the requested
commutator identity over each coefficient field, and the root-column formula
gives the degree-one coefficient identity. No adjoint equivariance is assumed.

Sources: `IntegralGeckConstruction`, `IntegralAllRootOperators`,
`GeckTitsRootWeight`, `GeckScalarExtensionCompatibility`, and Geck's root-system
identification described in `NoRootSums.AbsentWeights`.
-/

public section

namespace RootPairing.IntegralGeckConstruction
open Matrix
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma mapped_commutator_zero (i j : b.support) (w : List b.support)
    (h0 : P.root i + P.root (reflectionWord w j) ≠ 0)
    (hsum : P.root i + P.root (reflectionWord w j) ∉ Set.range P.root) :
    ⁅(eMatrix i).map (algebraMap ℤ R),
      (titsConjugate w (eMatrix j)).map (algebraMap ℤ R)⁆ = 0 := by
  apply weight_zero_of_absent (P.root i + P.root (reflectionWord w j)) h0 hsum
  · apply LieSubalgebra.lie_mem
    · rw [map_eMatrix]
      exact RootPairing.GeckConstruction.e_mem_lieAlgebra i
    · apply map_titsConjugate_mem_lieAlgebra
      rw [map_eMatrix]
      exact RootPairing.GeckConstruction.e_mem_lieAlgebra j
  · intro l
    have ha := map_titsConjugate_hasRootWeight (P := P) (b := b) [] i l
    simp only [reflectionWord, titsConjugate_apply, titsWord, titsWordInv_nil,
      one_mul, mul_one] at ha
    have hb := map_titsConjugate_hasRootWeight (P := P) (b := b) w j l
    rw [leibniz_lie, ha, hb, smul_lie, lie_smul, ← add_smul]
    simp only [map_add, LinearMap.add_apply, P.root_coroot_eq_pairing]

end
end RootPairing.IntegralGeckConstruction

namespace RootPairing.IntegralGeckConstruction
noncomputable section
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private def rootLatticeMap : P.rootSpan ℤ →+ (b.support → RatAlgClosure) where
  toFun x k := algebraMap ℤ RatAlgClosure (b.toWeightBasisInt.repr x k)
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp

omit [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
  [Fintype ι] [DecidableEq ι] in
private lemma rootLatticeMap_injective :
    Function.Injective (rootLatticeMap (P := P) (b := b)) := by
  intro x y h
  apply b.toWeightBasisInt.repr.injective
  ext k
  apply FaithfulSMul.algebraMap_injective ℤ RatAlgClosure
  exact congrFun h k

private lemma scalarExtension_no_sum {i j : ι}
    (h : P.root i + P.root j ∉ Set.range P.root) :
    (scalarExtension (P := P) (b := b)).root i +
        (scalarExtension (P := P) (b := b)).root j ∉
      Set.range (scalarExtension (P := P) (b := b)).root := by
  rintro ⟨k, hk⟩
  apply h
  refine ⟨k, ?_⟩
  have hspan : P.rootSpanMem ℤ k = P.rootSpanMem ℤ i + P.rootSpanMem ℤ j := by
    apply rootLatticeMap_injective (P := P) (b := b)
    rw [map_add]
    exact hk
  exact congrArg Subtype.val hspan

private lemma scalarExtension_sum_ne_zero {i j : ι}
    (h : P.root i + P.root j ≠ 0) :
    (scalarExtension (P := P) (b := b)).root i +
        (scalarExtension (P := P) (b := b)).root j ≠ 0 := by
  intro hk
  apply h
  have hspan : P.rootSpanMem ℤ i + P.rootSpanMem ℤ j = 0 := by
    apply rootLatticeMap_injective (P := P) (b := b)
    rw [map_add, map_zero]
    exact hk
  exact congrArg Subtype.val hspan

/-- A positive-simple integral Geck operator commutes with a Tits-transported
root operator when their root sum is nonzero and absent. -/
lemma integral_commutator_zero (i j : b.support) (w : List b.support)
    (h0 : P.root i + P.root (reflectionWord w j) ≠ 0)
    (hsum : P.root i + P.root (reflectionWord w j) ∉ Set.range P.root) :
    eMatrix i * titsConjugate w (eMatrix j) -
      titsConjugate w (eMatrix j) * eMatrix i = 0 := by
  have h0' := scalarExtension_sum_ne_zero (b := b) h0
  have hs' := scalarExtension_no_sum (b := b) hsum
  rw [← scalarExtension_reflectionWord (b := b) w j] at h0' hs'
  have h := mapped_commutator_zero (P := scalarExtension (P := P) (b := b))
    (b := scalarExtensionBase (P := P) (b := b)) i j w h0' hs'
  rw [scalarExtension_eMatrix, scalarExtension_eMatrix, scalarExtension_titsConjugate] at h
  change ⁅(eMatrix (P := P) i).map (algebraMap ℤ RatAlgClosure),
    (titsConjugate w (eMatrix j)).map (algebraMap ℤ RatAlgClosure)⁆ = 0 at h
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ RatAlgClosure)
  simpa only [Ring.lie_def, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_zero _ (map_zero _)] using h

end
end RootPairing.IntegralGeckConstruction

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- The actual positive-simple and root coordinate operators commute when the
root sum is absent and the roots are not opposite. -/
theorem positive_root_commutator_zero (m : ℕ)
    (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hopp : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hsum : typeF4RootPairing.root i + typeF4RootPairing.root r ∉
      Set.range typeF4RootPairing.root) :
    dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
      coordinateOperator m (Sum.inr r) * dividedPower m i 1 = 0 := by
  let := typeF4RootPairing.indexNeg
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have h0 : typeF4RootPairing.root i + typeF4RootPairing.root r ≠ 0 := by
    intro h
    apply hopp
    apply typeF4RootPairing.root.injective
    simpa only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
      typeF4RootPairing.reflection_apply_self] using eq_neg_of_add_eq_zero_right h
  have hi := integral_commutator_zero (P := typeF4RootPairing) i z.simple z.word
    (by simpa only [z.target] using h0) (by simpa only [z.target] using hsum)
  rw [coordinateOperator_eq_transport m r z.word z.simple z.target]
  simp only [dividedPower, eDividedPower_one]
  have hc := congrArg (fun A : Matrix Coordinate Coordinate ℤ =>
    A.map (Int.castRingHom (CoefficientField m))) hi
  simpa only [titsConjugate_apply, transportedMatrix, Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_zero _ (map_zero _)] using hc

/-- The absent-root-sum case of the degree-one coefficient identity. -/
theorem positive_root_coefficient_one_of_no_root_sum (m : ℕ)
    (i : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hopp : letI := typeF4RootPairing.indexNeg; r ≠ -(i : typeF4Roots))
    (hsum : typeF4RootPairing.root i + typeF4RootPairing.root r ∉
      Set.range typeF4RootPairing.root) :
    CoefficientIdentity m i (Sum.inr r) 1 := by
  rw [coefficientIdentity_one_iff, columnImage_one_root_zero m i r hopp hsum,
    positive_root_commutator_zero m i r hopp hsum]

end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
