module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.Preparation
public import Mathlib.LinearAlgebra.Trace

/-!
# Intrinsic spectral data for octad placement

The trace of a Golay sign of weight w is 24 - 2w, so the literal marked
octad has trace eight. Trace is unchanged by actual Leech conjugation.
For an order-three isometry, commutation modulo the two central signs
lifts to integral commutation: an anticommuting conjugate has the wrong cube.
Consequently quotient octad placement is equivalent to integral placement.

The integral cubic polynomial also gives the Eisenstein angle in every
orbit plane; positivity shows that a nonzero orbit spans a rank-two plane.
These are initial lattice facts for the remaining existence argument.

The final two propositions separate the geometric work still required:
construct a commuting trace-eight involution, and recognize such involutions
as conjugates of the marked Golay sign. Neither proposition is proved here.
Their application to the exact placement contract is in OctadPlacement.lean.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 (pp.132–134),
25.9 and Chapter 9 Exercise 6 (p.141), and 49.3–49.4 (pp.280–282).
The exercise concerns the specified cubic class, not its fixed-free converse.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The trace of the unique rational extension of an actual Leech isometry. -/
def rationalLeechTrace (t : LeechIsometryGroup) : ℚ :=
  LinearMap.trace ℚ RationalCoordinates (rationalExtension t.val).toLinearMap

/-- The rational extension of a Golay sign has the same coordinate formula. -/
theorem rationalExtension_sign_apply (c : golay) (x : RationalCoordinates) (i : Omega) :
    rationalExtension (signIsometry c).val x i = if c.val i = 0 then x i else -x i := by
  let f : RationalCoordinates →ₗ[ℚ] RationalCoordinates := {
    toFun := fun x i => if c.val i = 0 then x i else -x i
    map_add' := by intros; ext i; split_ifs <;> simp_all [add_comm]
    map_smul' := by intros; ext i; split_ifs <;> simp_all }
  have hf : f = (rationalExtension (signIsometry c).val).toLinearMap := by
    apply rationalExtension_unique
    intro y
    ext j
    change (if c.val j = 0 then (y.val j : ℚ) else -(y.val j : ℚ)) =
      ((if c.val j = 0 then y.val j else -y.val j : ℤ) : ℚ)
    split_ifs <;> simp
  exact (congrArg (fun q : RationalCoordinates →ₗ[ℚ] RationalCoordinates => q x i) hf).symm

/-- Compute the trace in the ordinary coordinate basis. -/
theorem rationalLeechTrace_sign (c : golay) :
    rationalLeechTrace (signIsometry c) = ∑ i : Omega, if c.val i = 0 then 1 else -1 := by
  rw [rationalLeechTrace, LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ Omega)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change rationalExtension (signIsometry c).val (Pi.single i 1) i = _
  rw [rationalExtension_sign_apply]
  simp

/-- Every negative coordinate subtracts two from the trace. -/
theorem rationalLeechTrace_sign_weight (c : golay) :
    rationalLeechTrace (signIsometry c) = 24 - 2 * (hammingNorm c.val : ℚ) := by
  rw [rationalLeechTrace_sign]
  classical
  have he (i : Omega) : (if c.val i = 0 then (1 : ℚ) else -1) =
      1 - 2 * (if c.val i ≠ 0 then 1 else 0) := by
    by_cases h : c.val i = 0 <;> norm_num [h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite]
  simp [hammingNorm, Fintype.card_prod, Fintype.card_fin]

/-- Trace is invariant under conjugation by an actual lattice isometry. -/
theorem rationalLeechTrace_conj (h t : LeechIsometryGroup) :
    rationalLeechTrace (MulAut.conj h t) = rationalLeechTrace t := by
  have he : fullIsometryExtension (MulAut.conj h t) =
      MulAut.conj (fullIsometryExtension h) (fullIsometryExtension t) := by
    simp [MulAut.conj_apply]
  have he' : rationalExtension (MulAut.conj h t).val =
      rationalExtension h.val * rationalExtension t.val * (rationalExtension h.val)⁻¹ :=
    congrArg Subtype.val he
  unfold rationalLeechTrace
  rw [he']
  exact LinearMap.trace_conj' (rationalExtension t.val).toLinearMap (rationalExtension h.val)


/-- Central signs do not hide an anticommuting lift of an odd-order cubic. -/
theorem cubic_projection_commute_iff {r t : LeechIsometryGroup} (hr : r ^ 3 = 1) :
    Commute (leechCentralProjection r) (leechCentralProjection t) ↔ Commute r t := by
  constructor
  · intro h
    have hk : MulAut.conj t r * r⁻¹ ∈ leechCentralSigns := by
      rw [← leechCentralProjection_kernel, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, MulAut.conj_apply]
      rw [← h.eq]
      simp [mul_assoc]
    have he : MulAut.conj t r = r := by
      rcases (leechCentralSigns_mem _).mp hk with he | he
      · exact mul_inv_eq_one.mp he
      · have he' : MulAut.conj t r = negationIsometry * r :=
          mul_inv_eq_iff_eq_mul.mp he
        have hc : Commute negationIsometry r :=
          (Subgroup.mem_center_iff.mp negation_mem_center r).symm
        have hp := congrArg (fun x : LeechIsometryGroup => x ^ 3) he'
        rw [← map_pow, hr, map_one, hc.mul_pow, hr, mul_one] at hp
        have hn : negationIsometry ^ 3 = negationIsometry := by
          rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two, negationIsometry_sq, one_mul]
        exact (negationIsometry_ne_one (hn.symm.trans hp.symm)).elim
    change r * t = t * r
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · exact fun h => h.map leechCentralProjection



/-- Orbit planes have the Eisenstein angle, in the literal integral pairing. -/
theorem cubic_orbit_pairing {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) (x : leech) :
    2 * integerDot x.val (r.val x).val = -integerDot x.val x.val := by
  have he := congrArg (fun y : leech => integerDot (r.val x).val y.val) (hp x)
  change integerDot (r.val x).val ((r.val (r.val x)).val + (r.val x).val + x.val) =
    integerDot (r.val x).val 0 at he
  rw [integerDot_add_right, integerDot_add_right, r.prop, r.prop,
    integerDot_comm (r.val x).val x.val] at he
  have hz : integerDot (r.val x).val 0 = 0 := by simp [integerDot]
  rw [hz] at he
  omega

/-- Each nonzero cubic orbit spans a genuine rank-two plane. -/
theorem cubic_orbit_independent {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0)
    {x : leech} (hx : x ≠ 0) {a b : ℤ}
    (hab : a • x + b • r.val x = 0) : a = 0 ∧ b = 0 := by
  have hpair := cubic_orbit_pairing hp x
  have hnorm : 0 < integerDot x.val x.val := by
    apply lt_of_le_of_ne (integerDot_self_nonneg _)
    intro he
    apply hx
    apply Subtype.ext
    exact (integerDot_self_zero _).mp he.symm
  have hleft := congrArg (fun y : leech => integerDot x.val y.val) hab
  have hright := congrArg (fun y : leech => integerDot (r.val x).val y.val) hab
  have dot_smul (u v : IntegerCoordinates) (n : ℤ) :
      integerDot u (n • v) = n * integerDot u v := by
    simp only [integerDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change integerDot x.val (a • x.val + b • (r.val x).val) = integerDot x.val 0 at hleft
  change integerDot (r.val x).val (a • x.val + b • (r.val x).val) =
    integerDot (r.val x).val 0 at hright
  rw [integerDot_add_right, dot_smul, dot_smul] at hleft hright
  rw [integerDot_comm (r.val x).val x.val, r.prop] at hright
  have hz (u : IntegerCoordinates) : integerDot u 0 = 0 := by simp [integerDot]
  rw [hz] at hleft hright
  have ha : (2 * a - b) * integerDot x.val x.val = 0 := by
    nlinarith [congrArg (fun z : ℤ => b * z) hpair]
  have hb : (2 * b - a) * integerDot x.val x.val = 0 := by
    nlinarith [congrArg (fun z : ℤ => a * z) hpair]
  have ha' := (mul_eq_zero.mp ha).resolve_right (ne_of_gt hnorm)
  have hb' := (mul_eq_zero.mp hb).resolve_right (ne_of_gt hnorm)
  omega


/-- The literal integral lift of the marked ambient octad. -/
def integralOctadSign : LeechIsometryGroup :=
  signEmbedding (Multiplicative.ofAdd (golayBasis 0))

theorem integralOctadSign_sq : integralOctadSign ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact signChange_involutive (golayBasis 0).val x.val

theorem integralOctadSign_trace : rationalLeechTrace integralOctadSign = 8 := by
  change rationalLeechTrace (signIsometry (golayBasis 0)) = 8
  rw [rationalLeechTrace_sign_weight, golay_octad_basis.2 0]
  norm_num

/-- Quotient placement is exactly integral placement for a cubic, with no sign ambiguity. -/
theorem octad_conjugator_iff_integral {r : LeechIsometryGroup} (hr : r ^ 3 = 1) :
    (∃ g : LeechCentralQuotient,
      Commute (MulAut.conj g (leechCentralProjection r)) ambientOctad) ↔
    ∃ h : LeechIsometryGroup, Commute (MulAut.conj h r) integralOctadSign := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨h, hh⟩ := leechCentralProjection_surjective g
    refine ⟨h, (cubic_projection_commute_iff ?_).mp ?_⟩
    · rw [← map_pow, hr, map_one]
    · simpa [MulAut.conj_apply, integralOctadSign, ambientOctad, hh] using hg
  · rintro ⟨h, hh⟩
    refine ⟨leechCentralProjection h, ?_⟩
    simpa [MulAut.conj_apply, integralOctadSign, ambientOctad] using
      hh.map leechCentralProjection

/-- An intrinsic involution condition on the actual rational Leech representation. -/
def TraceEightInvolution (t : LeechIsometryGroup) : Prop :=
  t ^ 2 = 1 ∧ rationalLeechTrace t = 8

/-- Remaining geometric recognition obligation; not asserted by this module. -/
def TraceEightInvolutionRecognition : Prop :=
  ∀ t : LeechIsometryGroup, TraceEightInvolution t →
    ∃ h : LeechIsometryGroup, MulAut.conj h t = integralOctadSign

/-- Remaining existence obligation: a commuting involution of trace eight,
without a chosen conjugacy class or a placement witness. -/
def IntegralCubicTraceEight : Prop :=
  ∀ r : LeechIsometryGroup, orderOf r = 3 →
    (∀ x : leech, r.val (r.val x) + r.val x + x = 0) →
    ∃ t : LeechIsometryGroup, TraceEightInvolution t ∧ Commute r t


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
