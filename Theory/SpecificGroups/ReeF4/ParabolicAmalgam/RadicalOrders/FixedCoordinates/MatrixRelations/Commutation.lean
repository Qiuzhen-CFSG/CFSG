module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Blocks
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums

/-!
# Commuting mixed-length F4 root curves

A long root and a short root with nonnegative inner product have a sum of
squared length at least three, whereas every F4 root has squared length at
most two. The associated integral operators commute: after scalar extension,
their commutator belongs to Geck's Lie algebra at that absent weight.
Cancelling factorials over the integers then gives commutation of all divided
powers, and hence of the actual specialized root curves.

This is the commuting-block calculation used in the Ree radical coordinates
underlying Aschbacher–Smith F.1.12(I)(5), `refs/quasithin.pdf`, p.263.
The integral construction and weight argument are those of
`IntegralAllRootOperators` and `NoRootSums`.
-/

public section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.MatrixRelations

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
noncomputable section

section Integral
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma mapped_commutator_zero [IsAlgClosed R]
    (w z : List b.support) (i j : b.support)
    (h0 : P.root (reflectionWord w i) + P.root (reflectionWord z j) ≠ 0)
    (hsum : P.root (reflectionWord w i) + P.root (reflectionWord z j) ∉
      Set.range P.root) :
    ⁅(titsConjugate w (eMatrix i)).map (algebraMap ℤ R),
      (titsConjugate z (eMatrix j)).map (algebraMap ℤ R)⁆ = 0 := by
  apply weight_zero_of_absent _ h0 hsum
  · apply LieSubalgebra.lie_mem
    all_goals
      apply map_titsConjugate_mem_lieAlgebra
      rw [map_eMatrix]
      apply RootPairing.GeckConstruction.e_mem_lieAlgebra
  · intro l
    rw [leibniz_lie, map_titsConjugate_hasRootWeight (P := P) w i l,
      map_titsConjugate_hasRootWeight (P := P) z j l,
      smul_lie, lie_smul, ← add_smul]
    simp only [map_add, LinearMap.add_apply, P.root_coroot_eq_pairing]

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

private lemma transported_operators_commute
    (w z : List b.support) (i j : b.support)
    (h0 : P.root (reflectionWord w i) + P.root (reflectionWord z j) ≠ 0)
    (hsum : P.root (reflectionWord w i) + P.root (reflectionWord z j) ∉
      Set.range P.root) :
    Commute (titsConjugate w (eMatrix i)) (titsConjugate z (eMatrix j)) := by
  have h0' := scalarExtension_sum_ne_zero (b := b) h0
  have hs' := scalarExtension_no_sum (b := b) hsum
  rw [← scalarExtension_reflectionWord (b := b) w i,
    ← scalarExtension_reflectionWord (b := b) z j] at h0' hs'
  have h := mapped_commutator_zero (P := scalarExtension (P := P) (b := b))
    (b := scalarExtensionBase (P := P) (b := b)) w z i j h0' hs'
  rw [scalarExtension_eMatrix, scalarExtension_eMatrix,
    scalarExtension_titsConjugate, scalarExtension_titsConjugate] at h
  change ⁅(titsConjugate (P := P) w (eMatrix i)).map (algebraMap ℤ RatAlgClosure),
    (titsConjugate (P := P) z (eMatrix j)).map (algebraMap ℤ RatAlgClosure)⁆ = 0 at h
  apply sub_eq_zero.mp
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ RatAlgClosure)
  simpa only [Ring.lie_def, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_zero _ (map_zero _)] using h

end Integral

/-- Positive integral root operators commute if their sum is nonzero and absent. -/
theorem positive_operators_commute (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (h0 : r.val + s.val ≠ 0)
    (hroot : r.val + s.val ∉ Set.range typeF4RootPairing.root) :
    Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s) := by
  let w := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  change Commute (rootOperator (P := typeF4RootPairing) r)
    (rootOperator (P := typeF4RootPairing) s)
  rw [rootOperator_of_pos r hr, rootOperator_of_pos s hs]
  exact transported_operators_commute w.word z.word w.simple z.simple
    (by simpa only [w.target, z.target, typeF4RootPairing_root] using h0)
    (by simpa only [w.target, z.target, typeF4RootPairing_root] using hroot)

/-- Factorial cancellation is performed integrally, so it is valid even when
factorials vanish in the eventual coefficient field. -/
theorem dividedPowers_commute_of_operators_commute (r s : F4Chevalley.Root)
    (h : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s)) (i j : ℕ) :
    Commute (F4Chevalley.integralOperators.rootDividedPower r i)
      (F4Chevalley.integralOperators.rootDividedPower s j) := by
  have hp := (h.pow_pow i j).eq
  rw [F4Chevalley.operator_pow_eq_factorial_smul,
    F4Chevalley.operator_pow_eq_factorial_smul] at hp
  simp only [smul_mul_assoc, mul_smul_comm] at hp
  change _ * _ = _ * _
  ext x y
  have hxy := congrFun (congrFun hp x) y
  change j.factorial • (i.factorial •
    ((F4Chevalley.integralOperators.rootDividedPower r i *
      F4Chevalley.integralOperators.rootDividedPower s j) x y)) =
    i.factorial • (j.factorial •
    ((F4Chevalley.integralOperators.rootDividedPower s j *
      F4Chevalley.integralOperators.rootDividedPower r i) x y)) at hxy
  simp only [nsmul_eq_mul] at hxy
  have hn : (i.factorial : ℤ) * j.factorial ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  convert hxy using 1 <;> ring

/-- Integral operator commutation implies root-curve commutation after any
commutative base change. -/
theorem rootCurves_commute_of_operators_commute {K : Type*} [CommRing K]
    (r s : F4Chevalley.Root)
    (h : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s)) (a b : K) :
    Commute (F4Chevalley.rootCurve r a) (F4Chevalley.rootCurve s b) := by
  have hc (i j : ℕ) : Commute
      (specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r i))
      (specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower s j)) := by
    have hp := congrArg (specializeMatrix (S := K))
      (dividedPowers_commute_of_operators_commute r s h i j).eq
    change _ * _ = _ * _
    simpa only [specializeMatrix_mul] using hp
  have hrow (i : ℕ) (u : K) : Commute
      (u • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r i))
      (F4Chevalley.rootCurve s b : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) := by
    rw [F4Chevalley.rootCurve_matrix_formula]
    exact (((Commute.one_right _).add_right ((hc i 1).smul_left u |>.smul_right b)).add_right
      ((hc i 2).smul_left u |>.smul_right (b ^ 2))).add_right
      ((hc i 3).smul_left u |>.smul_right (b ^ 3))
  apply Units.ext
  change _ * _ = _ * _
  rw [F4Chevalley.rootCurve_matrix_formula r]
  exact (((Commute.one_left _).add_left (hrow 1 a)).add_left (hrow 2 (a ^ 2))).add_left
    (hrow 3 (a ^ 3))

private theorem root_norm_le_two (r : F4Chevalley.Root) : dot r.val r.val ≤ 2 := by
  by_cases h : IsLongRoot r
  · rw [isLongRoot_norm r h]
  · rw [isShortRoot_norm r h]; norm_num

private theorem mixed_sum_norm (r s : F4Chevalley.Root)
    (hr : IsLongRoot r) (hs : IsShortRoot s) :
    dot (r.val + s.val) (r.val + s.val) = 3 + 2 * dot r.val s.val := by
  have he : dot s.val r.val = dot r.val s.val := by simp only [dot, mul_comm]
  change (r.val + s.val) ⬝ᵥ (r.val + s.val) = _
  simp only [add_dotProduct, dotProduct_add]
  change dot r.val r.val + dot s.val r.val +
    (dot r.val s.val + dot s.val s.val) = _
  rw [isLongRoot_norm r hr, isShortRoot_norm s hs, he]
  ring

/-- The sum of these mixed-length roots has squared length at least three. -/
theorem mixed_sum_absent (r s : F4Chevalley.Root)
    (hr : IsLongRoot r) (hs : IsShortRoot s) (hd : 0 ≤ dot r.val s.val) :
    r.val + s.val ≠ 0 ∧ r.val + s.val ∉ Set.range typeF4RootPairing.root := by
  have hn := mixed_sum_norm r s hr hs
  constructor
  · intro hz
    rw [hz] at hn
    have hz0 : dot (0 : Vec 4) 0 = 0 := by simp [dot]
    rw [hz0] at hn
    linarith
  · rintro ⟨t, ht⟩
    have hb := root_norm_le_two t
    change t.val = r.val + s.val at ht
    rw [ht, hn] at hb
    linarith

end
end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.MatrixRelations
