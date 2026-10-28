module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.MonomialLine

/-!
# Distinct extreme points of a nonconstant monomial curve

The minimum and maximum occupied weights have disjoint nonzero supports when
the weight interval has positive length. Their projective endpoint vectors are
therefore distinct, providing the final injectivity case in Borel §13.13.
-/

public noncomputable section

open scoped LinearAlgebra.Projectivization
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Finite ι]

theorem monomial_endpoints_ne
    (c : ι → k) (n : ι → ℕ) (N : ℕ) (hN : 0 < N)
    (hzero : ∃ i, n i = 0 ∧ c i ≠ 0) (hmax : ∃ i, n i = N ∧ c i ≠ 0) :
    monomialCurve c n hzero (affinePoint 0) ≠
      monomialCurve c (fun i => N - n i)
        (by obtain ⟨i, hi, hc⟩ := hmax; exact ⟨i, by simp [hi], hc⟩)
        (affinePoint 0) := by
  rw [monomialCurve_zero, monomialCurve_zero]
  intro h
  have he := (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mp h
  obtain ⟨r, hr⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp he
  obtain ⟨i, hi, hc⟩ := hzero
  have hh := congr_fun hr i
  simp only [Pi.smul_apply, smul_eq_mul, zeroCoordinates, hi, Nat.sub_zero,
    if_neg (Nat.ne_of_gt hN), mul_zero] at hh
  exact hc hh.symm

end Theory.AlgebraicGroup.Bor1.FlagCurve
