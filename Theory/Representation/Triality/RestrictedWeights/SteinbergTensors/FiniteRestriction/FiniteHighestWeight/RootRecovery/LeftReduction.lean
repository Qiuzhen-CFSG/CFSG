module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.RankOneInputs

/-!
# Reducing left D4 weight recovery to its two finite root orbits

The central left diagonal has exponent `a 1`. The three-arm diagonal has
exponent `a 0 + q * a 2 + q^2 * a 3`, where `q = 2^n`. Both follow from the
actual left-coroot evaluation equations, and the chosen highest vector is
fixed by the specified positive root products. The full restricted intervals
give bounds `q` and `q^3`, including `n = 1`; division into base-q digits then
recovers every coordinate.

An actual finite intertwiner pulls back along each compatible finite chart.
The final conditional theorem combines those pullbacks with the independent
rational SL2 recovery obligation. It does not assert existence of the charts
or prove that obligation. Those premises must be discharged before claiming
GLS3 2.8.2 / Steinberg §13.3(a). All raw convention diagnostics are preserved.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open scoped MatrixGroups

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
theorem RootOrbit.upperPoint_mem_positive (o : RootOrbit) (S : Geometry K)
    (n : ℕ) (t : k) :
    o.upperPoint S n t ∈ RootSubgroupGenerated S.roots S.roots.positive := by
  cases o with
  | central => exact rootPoint_mem_positive S 1 t
  | arms =>
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (rootPoint_mem_positive S 0 t) (rootPoint_mem_positive S 2 _))
      (rootPoint_mem_positive S 3 _)

omit [IsAlgClosed k] in
theorem RootOrbit.leftWeight_torusPoint (o : RootOrbit) (S : Geometry K)
    (n : ℕ) (a : Weight) (t : Variety.Point (KMult k)) :
    (S.leftWeightEmbedding a).pointCharacter (o.torusPoint S n t) =
      (dPointEquiv 1 t 0 : k) ^ o.degree n a := by
  cases o with
  | central => exact S.leftWeightEmbedding_coroot a 1 t
  | arms =>
    have he (i : Fin 4) := S.leftWeightEmbedding_coroot a i t
    change (S.leftWeightEmbedding a).pointCharacter
      ((S.leftSimpleCoroot 0).onPoints t * (S.leftSimpleCoroot 2).onPoints (t^(2^n)) *
        (S.leftSimpleCoroot 3).onPoints (t^((2^n)^2))) = _
    simp only [map_mul, map_pow, he]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      ← zpow_add₀ (dPointEquiv 1 t 0).ne_zero, ← zpow_add₀ (dPointEquiv 1 t 0).ne_zero]
    congr 1
    simp only [RootOrbit.degree, Nat.cast_pow, Nat.cast_ofNat]
    ring

theorem FiniteRootChart.highest_upper {S : Geometry K} {n : ℕ} {o : RootOrbit}
    (c : FiniteRootChart S n o) (A : RationalFactor K) {a : Weight} {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a)) (t : k) :
    (A.action.action (c.map.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)))).1 v = v := by
  rw [c.upper]
  exact highestVector_fixed_positiveRoots S A hv _ (o.upperPoint_mem_positive S n t)

theorem FiniteRootChart.highest_diagonal {S : Geometry K} {n : ℕ} {o : RootOrbit}
    (c : FiniteRootChart S n o) (A : RationalFactor K) {a : Weight} {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a))
    (t : Variety.Point (KMult k)) :
    (A.action.action (c.map.onPoints (standardSL2DiagonalMorphism.onPoints t))).1 v =
      (dPointEquiv 1 t 0 : k)^o.degree n a • v := by
  rw [c.diagonal, hv.2.2, o.leftWeight_torusPoint]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
theorem weight_eq_of_orbit_degrees {n : ℕ} {a b : Weight} (ha : InRestrictedRange n a) (hb : InRestrictedRange n b)
    (hc : a 1 = b 1)
    (h : a 0 + (2:ℤ)^n * a 2 + ((2:ℤ)^n)^2 * a 3 =
      b 0 + (2:ℤ)^n * b 2 + ((2:ℤ)^n)^2 * b 3) : a = b := by
  let q : ℤ := 2 ^ n
  have hq : 0 < q := pow_pos (by decide) _
  have hx : a 0 + q * (a 2 + q * a 3) = b 0 + q * (b 2 + q * b 3) := by
    dsimp [q]
    nlinarith only [h]
  have h0 : a 0 = b 0 := by
    have hh := congrArg (fun z : ℤ => z % q) hx
    simpa only [Int.add_mul_emod_self_left, q, Int.emod_eq_of_lt (ha 0).1 (ha 0).2,
      Int.emod_eq_of_lt (hb 0).1 (hb 0).2] using hh
  have h23 : a 2 + q * a 3 = b 2 + q * b 3 := by
    rw [h0, add_right_inj] at hx
    exact (mul_left_cancel₀ (ne_of_gt hq)) hx
  have h2 : a 2 = b 2 := by
    have hh := congrArg (fun z : ℤ => z % q) h23
    simpa only [Int.add_mul_emod_self_left, q, Int.emod_eq_of_lt (ha 2).1 (ha 2).2,
      Int.emod_eq_of_lt (hb 2).1 (hb 2).2] using hh
  have h3 : a 3 = b 3 := by
    rw [h2, add_right_inj] at h23
    exact (mul_left_cancel₀ (ne_of_gt hq)) h23
  funext i
  fin_cases i
  · exact h0
  · exact hc
  · exact h2
  · exact h3

theorem arms_degree_range {n : ℕ} {a : Weight} (ha : InRestrictedRange n a) :
    0 ≤ a 0 + (2:ℤ)^n * a 2 + ((2:ℤ)^n)^2 * a 3 ∧
    a 0 + (2:ℤ)^n * a 2 + ((2:ℤ)^n)^2 * a 3 < (2:ℤ)^(3*n) := by
  let q : ℤ := 2 ^ n
  have hq : 0 < q := pow_pos (by decide) _
  have hq2 : 0 ≤ q^2 := sq_nonneg q
  constructor
  · exact add_nonneg (add_nonneg (ha 0).1 (mul_nonneg (le_of_lt hq) (ha 2).1))
      (mul_nonneg hq2 (ha 3).1)
  · have h0 : a 0 ≤ q - 1 := by have := (ha 0).2; omega
    have h2 : a 2 ≤ q - 1 := by have := (ha 2).2; omega
    have h3 : a 3 ≤ q - 1 := by have := (ha 3).2; omega
    have hh := add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h2 (le_of_lt hq)))
      (mul_le_mul_of_nonneg_left h3 hq2)
    have hpow : (2:ℤ)^(3*n) = q^3 := by rw [Nat.mul_comm, pow_mul]
    rw [hpow]
    change a 0 + q * a 2 + q^2 * a 3 < q^3
    nlinarith only [hh]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

theorem RootOrbit.degree_range (o : RootOrbit) {n : ℕ} {a : Weight}
    (ha : InRestrictedRange n a) :
    0 ≤ o.degree n a ∧ o.degree n a < (2 : ℤ) ^ o.fieldExponent n := by
  cases o with
  | central => exact ha 1
  | arms => exact arms_degree_range ha

theorem FiniteRootChart.degree_eq_of_SL2_recovery
    (hSL : FiniteSL2HighestVectorRecovery (k := k))
    {S : Geometry K} {n : ℕ} {o : RootOrbit} (c : FiniteRootChart S n o)
    (A C : RationalFactor K) {a b : Weight}
    (ha : InRestrictedRange n a) (hb : InRestrictedRange n b)
    {v : A.Space} {w : C.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.leftWeightEmbedding a))
    (hw : HasHighWeight C.action S.bigCell.data.B S.torus w (S.leftWeightEmbedding b))
    (e : Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) (he : e v = w) : o.degree n a = o.degree n b := by
  obtain ⟨ρ, hρ, hrρ⟩ := rationalRepresentation_pullback_exists c.map A.action A.irreducible.1
  obtain ⟨τ, hτ, hrτ⟩ := rationalRepresentation_pullback_exists c.map C.action C.irreducible.1
  have hcard : (Nat.card c.field : ℤ) = (2 : ℤ) ^ o.fieldExponent n := by
    rw [c.card, Nat.cast_pow, Nat.cast_ofNat]
  apply hSL c.field A.Space C.Space ρ τ hrρ hrτ (o.degree n a) (o.degree n b)
    (o.degree_range ha).1 (by rw [hcard]; exact (o.degree_range ha).2)
    (o.degree_range hb).1 (by rw [hcard]; exact (o.degree_range hb).2)
    v w hv.1.1 hw.1.1
    (fun t => by rw [hρ]; exact c.highest_upper A hv t)
    (fun t => by rw [hτ]; exact c.highest_upper C hw t)
    (fun t => by rw [hρ]; exact c.highest_diagonal A hv t)
    (fun t => by rw [hτ]; exact c.highest_diagonal C hw t)
    e.toLinearEquiv he
  intro g x
  rw [hρ, hτ, ← c.finite_compat]
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (c.finiteMap g) x

/-- Conditional D4 assembly from actual finite charts and the independent
rational rank-one theorem. The chart and rank-one obligations remain explicit. -/
theorem leftHighestVectorWeightRecovery_of_finiteRootCharts
    (S : Geometry K) (n : ℕ)
    (charts : ∀ o : RootOrbit, Nonempty (FiniteRootChart S n o))
    (hSL : FiniteSL2HighestVectorRecovery (k := k)) : LeftHighestVectorWeightRecovery S n := by
  intro A C a b ha hb v w hv hw e he
  obtain ⟨central⟩ := charts .central
  obtain ⟨arms⟩ := charts .arms
  exact weight_eq_of_orbit_degrees ha hb
    (central.degree_eq_of_SL2_recovery hSL A C ha hb hv hw e he)
    (arms.degree_eq_of_SL2_recovery hSL A C ha hb hv hw e he)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.RootRecovery
