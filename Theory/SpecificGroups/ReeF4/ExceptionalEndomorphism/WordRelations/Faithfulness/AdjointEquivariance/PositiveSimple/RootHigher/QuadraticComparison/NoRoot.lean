module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.RootLine
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums.AbsentWeights
/-!
# Quadratic vanishing at an absent endpoint

The weight `r + 2i` is nonzero because a reduced root system has no root
`-2i`. The injective scalar-extension map on the integral root lattice
preserves this and the absence of a root at that weight. The quadratic
operator belongs to Geck's Lie algebra with precisely this weight, so the
general absent-weight theorem kills it in characteristic zero. Injectivity
of the integer embedding then gives integral vanishing.

Sources: the reduced-root-system axiom, the scalar extension in
`GeckScalarExtension`, and `NoRootSums.AbsentWeights`.
-/

public section
open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false
local notation "P₀" => scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)
local notation "b₀" => scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base)
local notation "K₀" => RatAlgClosure
set_option maxHeartbeats 800000

private def quadraticRootLatticeMap :
    typeF4RootPairing.rootSpan ℤ →+ (typeF4RootPairing_base.support → K₀) where
  toFun x k := algebraMap ℤ K₀ (typeF4RootPairing_base.toWeightBasisInt.repr x k)
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp

private lemma quadraticRootLatticeMap_injective :
    Function.Injective quadraticRootLatticeMap := by
  intro x y h
  apply typeF4RootPairing_base.toWeightBasisInt.repr.injective
  ext k
  apply FaithfulSMul.algebraMap_injective ℤ K₀
  exact congrFun h k

private lemma quadratic_weight_ne_zero (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    (P₀).root r + (2 : ℕ) • (P₀).root i ≠ 0 := by
  intro h
  have hspan : typeF4RootPairing.rootSpanMem ℤ r +
      (2 : ℕ) • typeF4RootPairing.rootSpanMem ℤ i = 0 := by
    apply quadraticRootLatticeMap_injective
    rw [map_add, map_nsmul, map_zero]
    exact h
  have hz : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i = 0 :=
    congrArg Subtype.val hspan
  let := typeF4RootPairing.indexNeg
  have : (2 : ℕ).AtLeastTwo := ⟨by omega⟩
  apply typeF4RootPairing.nsmul_notMem_range_root (n := 2) (i := i)
  refine ⟨-r, ?_⟩
  rw [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
    typeF4RootPairing.reflection_apply_self]
  calc
    -typeF4RootPairing.root r = -typeF4RootPairing.root r +
        (typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) := by rw [hz, add_zero]
    _ = _ := by abel

private lemma quadratic_weight_absent (i : typeF4RootPairing_base.support)
    (r : typeF4Roots)
    (hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉
      Set.range typeF4RootPairing.root) :
    (P₀).root r + (2 : ℕ) • (P₀).root i ∉ Set.range (P₀).root := by
  rintro ⟨k, hk⟩
  apply hr
  refine ⟨k, ?_⟩
  have hspan : typeF4RootPairing.rootSpanMem ℤ k =
      typeF4RootPairing.rootSpanMem ℤ r + (2 : ℕ) • typeF4RootPairing.rootSpanMem ℤ i := by
    apply quadraticRootLatticeMap_injective
    rw [map_add, map_nsmul]
    exact hk
  exact congrArg Subtype.val hspan

/-- With no second root endpoint, the integral quadratic operator vanishes.
The weight argument is applied in characteristic zero before descending to ℤ. -/
lemma integralQuadraticOperator_of_no_root (i : typeF4RootPairing_base.support)
    (r : typeF4Roots)
    (hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉
      Set.range typeF4RootPairing.root) :
    integralQuadraticOperator i r = 0 := by
  obtain ⟨hmem, hweight⟩ := integralQuadraticOperator_mem_weight i r
  have hz := weight_zero_of_absent (P := P₀) (b := b₀)
    ((P₀).root r + (2 : ℕ) • (P₀).root i) (quadratic_weight_ne_zero i r)
    (quadratic_weight_absent i r hr) hmem (by
      intro l
      rw [hweight l]
      congr 1
      simp only [map_add, LinearMap.add_apply,
        RootPairing.root_coroot_eq_pairing, two_smul, two_mul])
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ K₀)
  simpa only [Matrix.map_zero _ (map_zero _)] using hz

/-- The absent-endpoint case gives an unsigned comparison already over ℤ. -/
lemma integralQuadraticComparison_of_no_root (i : typeF4RootPairing_base.support)
    (r : typeF4Roots)
    (hr : typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i ∉
      Set.range typeF4RootPairing.root) :
    integralQuadraticOperator i r = integralQuadraticColumn i r := by
  rw [integralQuadraticOperator_of_no_root i r hr, integralQuadraticColumn_of_no_root i r hr]
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
