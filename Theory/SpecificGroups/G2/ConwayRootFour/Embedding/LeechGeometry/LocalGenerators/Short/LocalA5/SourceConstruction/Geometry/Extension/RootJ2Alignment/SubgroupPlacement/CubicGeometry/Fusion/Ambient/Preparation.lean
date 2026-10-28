module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Reduction

/-!
# Integral lifts and the marked octad route for Leech cubic fusion

Binary fixed-freeness excludes integral fixed vectors by repeated division by
2 in the actual lattice. An order-three element of the central quotient has
an order-three lift: multiply an arbitrary lift by central negation if needed.
Its orbit sum is fixed, hence zero, giving the integral Eisenstein polynomial.
Conversely that polynomial reduces to binary fixed-freeness. No comparison
with a chosen Eisenstein representative or its conjugacy class is assumed.

The first Golay basis octad marks a concrete involution in the central quotient.
The propositions at the end isolate the remaining geometric placement and
local centralizer fusion obligations; neither is asserted here. The integral
placement adapter is an application of the polynomial-lift theorem to the
literal quotient map and the whole binary Leech module.

Source: Aschbacher, *Sporadic Groups* (1994), 25.9 and Chapter 9,
Exercise 6 (p.141), Sections 46 and 49, especially 49.1–49.3 (pp.280–281).
The exercise proves fixed-freeness for the specified class; its converse
requires the remaining placement and local fusion arguments.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

private theorem leech_double_injective : Function.Injective (fun x : leech => (2 : ℕ) • x) := by
  intro x y h
  apply Subtype.ext
  ext i
  have hi := congrArg (fun z : leech => z.val i) h
  change (2 : ℤ) * x.val i = 2 * y.val i at hi
  omega

/-- Binary fixed-freeness excludes fixed vectors on the integral lattice. -/
theorem integral_fixed_eq_zero {r : LeechIsometryGroup}
    (hf : CubicFixedFree (leechCentralProjection r)) {x : leech}
    (hx : r.val x = x) : x = 0 := by
  have half : ∀ y : leech, r.val y = y →
      ∃ z : leech, (2 : ℕ) • z = y ∧ r.val z = z := by
    intro y hy
    have hred : leechReduction y = 0 := hf _ (by
      rw [quotientModTwoRepresentation_compatible, leechModTwoRepresentation_reduce, hy])
    obtain ⟨z, hz⟩ := (leechReduction_eq_zero y).mp hred
    refine ⟨z, hz, leech_double_injective ?_⟩
    change (2 : ℕ) • r.val z = (2 : ℕ) • z
    rw [← map_nsmul, hz, hy]
  have divisible : ∀ n : ℕ, ∃ y : leech, (2 ^ n : ℕ) • y = x ∧ r.val y = y := by
    intro n
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, hy, hfy⟩ := ih
      obtain ⟨z, hz, hfz⟩ := half y hfy
      refine ⟨z, ?_, hfz⟩
      rw [pow_succ', mul_nsmul, hz, hy]
  apply Subtype.ext
  ext i
  obtain ⟨y, hy, _⟩ := divisible (x.val i).natAbs
  have hd : ((2 ^ (x.val i).natAbs : ℕ) : ℤ) ∣ x.val i := by
    refine ⟨y.val i, ?_⟩
    exact (congrArg (fun z : leech => z.val i) hy).symm
  have hn := Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.mp hd) Nat.lt_two_pow_self
  exact Int.natAbs_eq_zero.mp hn

/-- Every cubic of the central quotient has a genuine order-three integral lift. -/
theorem exists_order_three_lift {a : LeechCentralQuotient} (ha : orderOf a = 3) :
    ∃ r : LeechIsometryGroup, leechCentralProjection r = a ∧ orderOf r = 3 := by
  obtain ⟨r, hr⟩ := leechCentralProjection_surjective a
  have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have hr3 : r ^ 3 ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel, MonoidHom.mem_ker, map_pow, hr, ha3]
  have hn : leechCentralProjection negationIsometry = 1 := by
    change negationIsometry ∈ leechCentralProjection.ker
    rw [leechCentralProjection_kernel]
    exact Subgroup.mem_zpowers _
  have hnontrivial : a ≠ 1 := by intro h; simp [h] at ha
  rcases (leechCentralSigns_mem _).mp hr3 with h | h
  · refine ⟨r, hr, orderOf_eq_prime h ?_⟩
    intro he
    exact hnontrivial (hr.symm.trans (by simp [he]))
  · have hc : Commute r negationIsometry := (Subgroup.mem_center_iff.mp negation_mem_center r)
    have hc3 : (r * negationIsometry) ^ 3 = 1 := by
      rw [hc.mul_pow, h]
      simp only [pow_succ, pow_zero, one_mul, negationIsometry_sq]
    refine ⟨r * negationIsometry, by rw [map_mul, hr, hn, mul_one],
      orderOf_eq_prime hc3 ?_⟩
    intro he
    have := congrArg leechCentralProjection he
    simp only [map_mul, hr, hn, mul_one, map_one] at this
    exact hnontrivial this

/-- The integral lift satisfies the Eisenstein polynomial, on every lattice vector. -/
theorem integral_cubic_polynomial {r : LeechIsometryGroup} (hr : orderOf r = 3)
    (hf : CubicFixedFree (leechCentralProjection r)) (x : leech) :
    r.val (r.val x) + r.val x + x = 0 := by
  apply integral_fixed_eq_zero hf
  have hc : r.val (r.val (r.val x)) = x := by
    have hp : r ^ 3 = 1 := hr ▸ pow_orderOf_eq_one r
    exact congrArg (fun g : LeechIsometryGroup => g.val x) hp
  simp only [map_add, hc]
  abel

/-- Fixed-free cubics have polynomial integral lifts, with the literal quotient map. -/
theorem exists_polynomial_lift {a : LeechCentralQuotient} (ha : orderOf a = 3)
    (hf : CubicFixedFree a) :
    ∃ r : LeechIsometryGroup, leechCentralProjection r = a ∧ orderOf r = 3 ∧
      ∀ x : leech, r.val (r.val x) + r.val x + x = 0 := by
  obtain ⟨r, hr, ho⟩ := exists_order_three_lift ha
  exact ⟨r, hr, ho, integral_cubic_polynomial ho (hr.symm ▸ hf)⟩

/-- Conversely, the integral polynomial identity implies binary fixed-freeness. -/
theorem cubicFixedFree_of_integral_polynomial {r : LeechIsometryGroup}
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    CubicFixedFree (leechCentralProjection r) := by
  intro v hv
  rw [quotientModTwoRepresentation_compatible] at hv
  obtain ⟨x, rfl⟩ := leechReduction_surjective v
  have hs := congrArg leechReduction (hp x)
  simp only [map_add, map_zero, ← leechModTwoRepresentation_reduce, hv] at hs
  have htwo : leechReduction x + leechReduction x = 0 := by
    calc
      _ = (2 : Bit) • leechReduction x := (two_smul Bit _).symm
      _ = 0 := by rw [show (2 : Bit) = 0 by decide, zero_smul]
  simpa only [htwo, zero_add] using hs

/-- The binary and integral criteria agree for every order-three integral isometry. -/
theorem cubicFixedFree_iff_integral_polynomial {r : LeechIsometryGroup}
    (hr : orderOf r = 3) :
    CubicFixedFree (leechCentralProjection r) ↔
      ∀ x : leech, r.val (r.val x) + r.val x + x = 0 :=
  ⟨integral_cubic_polynomial hr, cubicFixedFree_of_integral_polynomial⟩

/-- The concrete octad sign used to mark the local centralizer. -/
def ambientOctad : LeechCentralQuotient :=
  leechCentralProjection (signEmbedding (Multiplicative.ofAdd (golayBasis 0)))

theorem ambientOctad_weight : hammingNorm (golayBasis 0 : BinaryWord) = 8 :=
  golay_octad_basis.2 0

theorem ambientOctad_order : orderOf ambientOctad = 2 := by
  apply orderOf_eq_prime
  · have hs : signEmbedding (Multiplicative.ofAdd (golayBasis 0)) ^ 2 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      exact signChange_involutive (golayBasis 0).val x.val
    rw [ambientOctad, ← map_pow, hs, map_one]
  · intro h
    have hm : signEmbedding (Multiplicative.ofAdd (golayBasis 0)) ∈ leechCentralSigns := by
      rw [← leechCentralProjection_kernel]
      exact h
    rcases (leechCentralSigns_mem _).mp hm with he | he
    · have he' := signEmbedding_injective (he.trans signEmbedding.map_one.symm)
      have hz : (golayBasis 0 : BinaryWord) = 0 :=
        congrArg (fun c : Multiplicative golay => c.toAdd.val) he'
      have hw := ambientOctad_weight
      rw [hz] at hw
      have hzero : hammingNorm (0 : BinaryWord) = 0 := by simp
      omega
    · have he' := signEmbedding_injective (he.trans allOnes_sign_negation.symm)
      have ho : (golayBasis 0 : BinaryWord) = allOnes :=
        congrArg (fun c : Multiplicative golay => c.toAdd.val) he'
      have hw := ambientOctad_weight
      rw [ho] at hw
      have hones : hammingNorm allOnes = 24 := by decide
      omega

/-- The whole binary fixed-space condition is preserved by actual ambient conjugation. -/
theorem cubicFixedFree_conj {a : LeechCentralQuotient} (hf : CubicFixedFree a)
    (g : LeechCentralQuotient) : CubicFixedFree (MulAut.conj g a) := by
  intro v hv
  let u := (quotientModTwoRepresentation g).symm v
  have hu : quotientModTwoRepresentation a u = u := by
    apply (quotientModTwoRepresentation g).injective
    have he : quotientModTwoRepresentation (MulAut.conj g a) v =
        quotientModTwoRepresentation g (quotientModTwoRepresentation a u) := by
      simp [MulAut.conj_apply, map_mul, u]
    rw [← he, hv]
    exact ((quotientModTwoRepresentation g).apply_symm_apply v).symm
  have hz := hf u hu
  have := congrArg (quotientModTwoRepresentation g) hz
  simpa [u] using this

/-- Geometric placement into the centralizer of the marked octad involution.
This proposition is a remaining obligation, not a proved class characterization. -/
def OctadPlacement : Prop :=
  ∀ a : LeechCentralQuotient, orderOf a = 3 → CubicFixedFree a →
    ∃ g : LeechCentralQuotient, Commute (MulAut.conj g a) ambientOctad

/-- Local fusion inside the literal octad centralizer. This is a separate
remaining obligation and does not assume ambient fusion. -/
def OctadLocalFusion : Prop :=
  ∀ a b : LeechCentralQuotient,
    Commute a ambientOctad → Commute b ambientOctad →
    orderOf a = 3 → orderOf b = 3 → CubicFixedFree a → CubicFixedFree b →
    ∃ c : LeechCentralQuotient, Commute c ambientOctad ∧
      Subgroup.zpowers a = (Subgroup.zpowers b).map (MulAut.conj c).toMonoidHom

/-- The remaining geometric statement in integral form. The polynomial is an
identity on the actual Leech lattice, not merely an abstract linear operator. -/
def IntegralOctadPlacement : Prop :=
  ∀ r : LeechIsometryGroup, orderOf r = 3 →
    (∀ x : leech, r.val (r.val x) + r.val x + x = 0) →
    ∃ g : LeechCentralQuotient,
      Commute (MulAut.conj g (leechCentralProjection r)) ambientOctad

/-- Apply integral placement to the order-three lift of an arbitrary binary
fixed-free cubic. This discharges the change-of-model premises exactly. -/
theorem octadPlacement_of_integral (h : IntegralOctadPlacement) : OctadPlacement := by
  intro a ha hf
  obtain ⟨r, hr, ho, hp⟩ := exists_polynomial_lift ha hf
  simpa only [hr] using h r ho hp

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
