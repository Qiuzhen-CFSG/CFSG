module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.MonomialLine

/-!
# A positive occupied weight makes the monomial curve nonconstant

The positive-weight coordinate vanishes at parameter zero and is nonzero at
parameter one. Homogeneous ideal membership distinguishes the two actual
projective points, supplying the source density input for Borel §13.13.
-/

public noncomputable section

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Finite ι]

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
theorem monomialCurve_zero_ne_one
    (c : ι → k) (n : ι → ℕ) (hzero : ∃ i, n i = 0 ∧ c i ≠ 0)
    (b : ι) (hb : n b ≠ 0) (hcb : c b ≠ 0) :
    monomialCurve c n hzero (affinePoint 0) ≠ monomialCurve c n hzero (affinePoint 1) := by
  intro h
  have hm : MvPolynomial.X b ∈
      ((monomialCurve c n hzero).hom ((affinePoint 0).1 (IsLocalRing.closedPoint k))).asHomogeneousIdeal := by
    exact (curve_mem_iff (monomialCoordinates c n) (monomialCoordinates_unit c n hzero) 0
      (MvPolynomial.isHomogeneous_X k b)).mpr (by simp [monomialCoordinates, hb])
  have hp := congrArg (fun p : Point (projectiveSpaceByCoordinates k ι) =>
    p.1 (IsLocalRing.closedPoint k)) h
  change MvPolynomial.X b ∈
    ((monomialCurve c n hzero (affinePoint 0)).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal at hm
  rw [hp] at hm
  have hz := (curve_mem_iff (monomialCoordinates c n) (monomialCoordinates_unit c n hzero) 1
    (MvPolynomial.isHomogeneous_X k b)).mp hm
  exact hcb (by simpa [monomialCoordinates] using hz)

end Theory.AlgebraicGroup.Bor1.FlagCurve
