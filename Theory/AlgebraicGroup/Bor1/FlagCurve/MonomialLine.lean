module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.LineGluing

/-!
# Global projective monomial curves

The two extreme-weight parametrizations have reciprocal parameters on their
common nonzero orbit. They therefore glue to an actual morphism from the
projective line, with both original affine chart identities. This construction
is independent of characteristic and is used after gcd normalization in the
proof of Borel, Linear Algebraic Groups, §13.13.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Finite ι]

theorem monomialCurve_reciprocal
    (c : ι → k) (n : ι → ℕ) (N : ℕ)
    (hzero : ∃ i, n i = 0 ∧ c i ≠ 0)
    (hmax : ∃ i, n i = N ∧ c i ≠ 0)
    (hbound : ∀ i, n i ≤ N)
    (a : k) (ha : a ≠ 0) :
    monomialCurve c n hzero (affinePoint a) =
      monomialCurve c (fun i => N - n i)
        (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩)
        (affinePoint a⁻¹) := by
  obtain ⟨hv, he⟩ := monomialCurve_point c n hzero a
  obtain ⟨hw, hf⟩ := monomialCurve_point c (fun i => N - n i)
    (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩) a⁻¹
  rw [he, hf]
  apply (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mpr
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨a ^ N, ?_⟩
  funext i
  change a ^ N * (c i * a⁻¹ ^ (N - n i)) = c i * a ^ n i
  rw [show N = n i + (N - n i) from (Nat.add_sub_of_le (hbound i)).symm,
    pow_add]
  have hc : a ^ (N - n i) * a⁻¹ ^ (N - n i) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  calc
    a ^ n i * a ^ (N - n i) * (c i * a⁻¹ ^ (n i + (N - n i) - n i)) =
      c i * a ^ n i * (a ^ (N - n i) * a⁻¹ ^ (N - n i)) := by
        rw [Nat.add_sub_cancel_left]
        ring
    _ = c i * a ^ n i := by rw [hc, mul_one]

noncomputable def monomialProjectiveCurve
    (c : ι → k) (n : ι → ℕ) (N : ℕ)
    (hzero : ∃ i, n i = 0 ∧ c i ≠ 0)
    (hmax : ∃ i, n i = N ∧ c i ≠ 0)
    (hbound : ∀ i, n i ≤ N) :
    Morphism (projectiveLine k) (projectiveSpaceByCoordinates k ι) :=
  glueProjectiveLine (fun i : Fin 2 => if i = 0 then monomialCurve c n hzero
    else monomialCurve c (fun i => N - n i)
      (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩))
    (by simpa using monomialCurve_reciprocal c n N hzero hmax hbound)

theorem monomialProjectiveCurve_chart_zero
    (c : ι → k) (n : ι → ℕ) (N : ℕ)
    (hzero : ∃ i, n i = 0 ∧ c i ≠ 0)
    (hmax : ∃ i, n i = N ∧ c i ≠ 0)
    (hbound : ∀ i, n i ≤ N) :
    (projectiveLineChartInclusion (k := k) 0).comp
      (monomialProjectiveCurve c n N hzero hmax hbound) = monomialCurve c n hzero := by
  exact glueProjectiveLine_chart _ _ 0

theorem monomialProjectiveCurve_chart_one
    (c : ι → k) (n : ι → ℕ) (N : ℕ)
    (hzero : ∃ i, n i = 0 ∧ c i ≠ 0)
    (hmax : ∃ i, n i = N ∧ c i ≠ 0)
    (hbound : ∀ i, n i ≤ N) :
    (projectiveLineChartInclusion (k := k) 1).comp
      (monomialProjectiveCurve c n N hzero hmax hbound) =
      monomialCurve c (fun i => N - n i)
        (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩) := by
  unfold monomialProjectiveCurve
  simpa only [show (1 : Fin 2) ≠ 0 from by decide, if_false] using glueProjectiveLine_chart
    (fun i : Fin 2 => if i = 0 then monomialCurve c n hzero
      else monomialCurve c (fun i => N - n i)
        (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩))
    (by simpa using monomialCurve_reciprocal c n N hzero hmax hbound) 1

end Theory.AlgebraicGroup.Bor1.FlagCurve
