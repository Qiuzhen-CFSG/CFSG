module

public import Theory.AlgebraicGroup.Variety.ProjectivePolynomialCurve

/-!
# Weighted coordinate limits

For nonzero coordinates `v` and integral weights `m`, choose the largest
occupied weight `M`. The polynomials `v i * t^(M-m i)` have a constant nonzero
coordinate. Their projective curve at zero is exactly the highest-weight
projection, and away from zero it is the weighted orbit evaluated at `t⁻¹`.

The arbitrary nonnegative-exponent curve is also exposed for normalized monomial
parametrizations of projective curves. Source: Borel, IV, 13.3 and 13.8.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit

universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

def monomialCoordinates (v : ι → k) (n : ι → ℕ) : ι → Polynomial k :=
  fun i => Polynomial.C (v i) * Polynomial.X ^ n i

omit [Finite ι] in
theorem monomialCoordinates_unit (v : ι → k) (n : ι → ℕ)
    (h : ∃ i, n i = 0 ∧ v i ≠ 0) : ∃ i, IsUnit (monomialCoordinates v n i) := by
  obtain ⟨i, hn, hv⟩ := h
  refine ⟨i, ?_⟩
  simpa [monomialCoordinates, hn] using
    (isUnit_iff_ne_zero.mpr hv).map (Polynomial.C : k →+* Polynomial k)

def monomialCurve (v : ι → k) (n : ι → ℕ)
    (h : ∃ i, n i = 0 ∧ v i ≠ 0) :
    Morphism (polynomialAffineLine k) (projectiveSpaceByCoordinates k ι) :=
  ProjectivePolynomialCurve.curve (monomialCoordinates v n) (monomialCoordinates_unit v n h)

def zeroCoordinates (v : ι → k) (n : ι → ℕ) : ι → k :=
  fun i => if n i = 0 then v i else 0

omit [Finite ι] in
theorem zeroCoordinates_ne_zero (v : ι → k) (n : ι → ℕ)
    (h : ∃ i, n i = 0 ∧ v i ≠ 0) : zeroCoordinates v n ≠ 0 := by
  obtain ⟨i, hi, hv⟩ := h
  intro hz
  exact hv (by simpa [zeroCoordinates, hi] using congr_fun hz i)

omit [Finite ι] in
theorem monomial_eval_zero (v : ι → k) (n : ι → ℕ) :
    (fun i => (monomialCoordinates v n i).eval 0) = zeroCoordinates v n := by
  funext i
  by_cases hi : n i = 0 <;> simp [monomialCoordinates, zeroCoordinates, hi]

variable [IsAlgClosed k]

theorem monomialCurve_zero (v : ι → k) (n : ι → ℕ)
    (h : ∃ i, n i = 0 ∧ v i ≠ 0) :
    monomialCurve v n h (ProjectivePolynomialCurve.affinePoint 0) =
      projectivePointOfVector (zeroCoordinates v n) (zeroCoordinates_ne_zero v n h) := by
  rw [monomialCurve, ProjectivePolynomialCurve.curve_point]
  simp only [monomial_eval_zero]
  rfl

theorem monomialCurve_point (v : ι → k) (n : ι → ℕ)
    (h : ∃ i, n i = 0 ∧ v i ≠ 0) (a : k) :
    ∃ hv : (fun i => v i * a ^ n i) ≠ 0,
      monomialCurve v n h (ProjectivePolynomialCurve.affinePoint a) =
        projectivePointOfVector (fun i => v i * a ^ n i) hv := by
  have heq : (fun i => (monomialCoordinates v n i).eval a) =
      (fun i => v i * a ^ n i) := by simp [monomialCoordinates]
  have hv := ProjectivePolynomialCurve.eval_ne_zero (monomialCoordinates v n)
    (monomialCoordinates_unit v n h) a
  rw [heq] at hv
  refine ⟨hv, ?_⟩
  rw [monomialCurve, ProjectivePolynomialCurve.curve_point]
  simp only [heq]
  rfl

def topCoordinates (v : ι → k) (m : ι → ℤ) (M : ℤ) : ι → k :=
  fun i => if m i = M then v i else 0

omit [Finite ι] [IsAlgClosed k] in
theorem topCoordinates_eq_zeroCoordinates (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (hM : ∀ i, v i ≠ 0 → m i ≤ M) :
    topCoordinates v m M = zeroCoordinates v (fun i => (M - m i).toNat) := by
  funext i
  by_cases hv : v i = 0
  · simp [topCoordinates, zeroCoordinates, hv]
  · have hm := hM i hv
    have heq : (M - m i).toNat = 0 ↔ m i = M := by omega
    simp [topCoordinates, zeroCoordinates, heq]

omit [Finite ι] [IsAlgClosed k] in
theorem topCoordinates_ne_zero (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) : topCoordinates v m M ≠ 0 := by
  obtain ⟨i, hi, hv⟩ := h
  intro hz
  exact hv (by simpa [topCoordinates, hi] using congr_fun hz i)

omit [Finite ι] [IsAlgClosed k] in
theorem topExponent_exists (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) :
    ∃ i, (M - m i).toNat = 0 ∧ v i ≠ 0 := by
  obtain ⟨i, hi, hv⟩ := h
  exact ⟨i, by simp [hi], hv⟩

def topCurve (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) :
    Morphism (polynomialAffineLine k) (projectiveSpaceByCoordinates k ι) :=
  monomialCurve v (fun i => (M - m i).toNat) (topExponent_exists v m M h)

theorem topCurve_zero (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) (hM : ∀ i, v i ≠ 0 → m i ≤ M) :
    topCurve v m M h (ProjectivePolynomialCurve.affinePoint 0) =
      projectivePointOfVector (topCoordinates v m M) (topCoordinates_ne_zero v m M h) := by
  rw [topCurve, monomialCurve_zero]
  simp only [← topCoordinates_eq_zeroCoordinates v m M hM]
  rfl

omit [Finite ι] [IsAlgClosed k] in
theorem topCurve_coordinates_nonzero (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (hM : ∀ i, v i ≠ 0 → m i ≤ M) (a : k) (ha : a ≠ 0) :
    (fun i => v i * a ^ (M - m i).toNat) =
      a ^ M • (fun i => v i * (a⁻¹) ^ m i) := by
  funext i
  by_cases hv : v i = 0
  · simp [hv]
  · have hm : 0 ≤ M - m i := sub_nonneg.mpr (hM i hv)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← zpow_natCast, Int.toNat_of_nonneg hm, zpow_sub₀ ha, inv_zpow]
    ring

omit [IsAlgClosed k] in
private theorem projectivePoint_congr {v w : ι → k} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : v = w) : projectivePointOfVector v hv = projectivePointOfVector w hw := by
  subst w
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem topCurve_point_nonzero (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) (hM : ∀ i, v i ≠ 0 → m i ≤ M)
    (a : k) (ha : a ≠ 0) :
    ∃ hv : (fun i => v i * (a⁻¹) ^ m i) ≠ 0,
      topCurve v m M h (ProjectivePolynomialCurve.affinePoint a) =
        projectivePointOfVector (fun i => v i * (a⁻¹) ^ m i) hv := by
  obtain ⟨hv, heq⟩ := monomialCurve_point v (fun i => (M - m i).toNat)
    (topExponent_exists v m M h) a
  have hcoords := topCurve_coordinates_nonzero v m M hM a ha
  have hv' : (fun i => v i * (a⁻¹) ^ m i) ≠ 0 := by
    intro hz
    apply hv
    rw [hcoords, hz, smul_zero]
  refine ⟨hv', ?_⟩
  have hp := projectivePoint_congr hv (smul_ne_zero (zpow_ne_zero M ha) hv') hcoords
  exact heq.trans (hp.trans (projectivePointOfVector_smul _ hv' (a ^ M) (zpow_ne_zero _ ha)))

theorem topCoordinates_mem_closed (v : ι → k) (m : ι → ℤ) (M : ℤ)
    (h : ∃ i, m i = M ∧ v i ≠ 0) (hM : ∀ i, v i ≠ 0 → m i ≤ M)
    {Z : Set (projectiveSpaceByCoordinates k ι).toScheme} (hZ : IsClosed Z)
    (horbit : ∀ (a : k) (_ha : a ≠ 0) (hv : (fun i => v i * a ^ m i) ≠ 0),
      (projectivePointOfVector (fun i => v i * a ^ m i) hv).1
        (IsLocalRing.closedPoint k) ∈ Z) :
    (projectivePointOfVector (topCoordinates v m M) (topCoordinates_ne_zero v m M h)).1
      (IsLocalRing.closedPoint k) ∈ Z := by
  rw [← topCurve_zero v m M h hM]
  apply ProjectivePolynomialCurve.curve_zero_mem_of_nonzero _
    (monomialCoordinates_unit v _ (topExponent_exists v m M h)) hZ
  intro a ha
  obtain ⟨hv, heq⟩ := topCurve_point_nonzero v m M h hM a ha
  change (topCurve v m M h _).1 _ ∈ Z
  rw [heq]
  exact horbit a⁻¹ (inv_ne_zero ha) hv

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
