module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianSeed

/-!
# Components in the natural branch of 12.9

All clauses of source 12.9.3 are proved for the original degrees four and
five. The point component has exactly the source alternatives; every other
specified component equals its literal Lᵢ, with relative normality in Gᵢ.
The comparisons use the original embedded quotient maps and full Sylows.
The seven-radical argument excludes three-space enlargements, using an
actual odd-Sylow pair for Held, whose seven-rank is two.

The original center quotient is now irreducible under L₀, by transport
through the selected conjugation and its exact action kernel. The returning
center does not centralize Z(U), so its centralizer in Z(U) is exactly
(Z(U) intersect Z(U)^g)V₁, of index four. The source seed
Ω₁(Z(T)) intersect Z(I₂) is nontrivial and is moved by K₁. Its literal
orbit in Z(U) is reduced in K₁T and supplies a chosen constituent, proving
faithful local membership. The exact point-component two-core quotient
maps isomorphically onto the dotted A₈ actor, retaining the original
projection. Every chosen constituent in Z(U) covers the center quotient
and has returning-center fixed subgroup of index four. Maximality, the
NaturalReduction 4 application and the orthogonal contradiction remain.

The abelian point span is already proved when L₁ is normal in G₁. The
nonabelian action comparisons exclude twelve printed G.11 rows and the
exceptional full GL₄(2) row, using the original point residual and full
quotient Sylow. The A₇ exclusion has no remaining geometric premises.
Only the split orthogonal six-space survives, in original degree four;
its actual A₈ action, full point-component image and nontrivial conjugate
center are proved. Degree-five abelianity follows conditionally from a
catalogue witness. Exhaustion and the orthogonal contradiction remain.
The original nonabelian flag now supplies all G.10 hypotheses, relative
Sylow normality and the actual SQTK cover. In the orthogonal row, the seed
image equals the three-dimensional isotropic intersection, and the
conjugate-center image is exactly the actor kernel on this seed. It lies
in both literal parabolic two-cores. The point residual and full quotient
Sylow exhaust the seed stabilizer of index fifteen and order 1344. The
conjugation map identifies the dotted conjugate center with the original
center modulo its intersection with the conjugate center and V₁. The point
residual induces full GL₃(2) on the seed, and the exact parabolic intersection
normalizes the conjugate-center image. Hyperplane displacement and the
point-stabilizer action make that image an irreducible four-group. The original
center quotient in source equation (*) therefore has order four. The
literal L₀ = O²(C_L(V₂)) equals O²(C_{L₁}(V₂)), and L₀T is exactly
L₁T ∩ G₂ and the opposite end-node ordered parabolic in degree four.
Its dotted image with the original Sylow is the same parabolic intersection;
the four-group is already irreducible under dotted L₀. The original P, I₂
and selected g normalize L₀. The center-quotient action transport is
proved; the natural-four-module contradiction remains.
The remaining nonnormal abelianity argument supplies the sole premise below;
the complete component geometry is constructed here. Local control remains
with the same natural-source owner.

Source: Aschbacher--Smith 12.9.3--4, printed pp.858--860.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u

/-- Apply the completed component theorem to the original 12.9.3--4 contract.
The remaining 12.9.4 premise retains every original hypothesis, including the
independently supplied degree-four natural reduction. -/
theorem componentInput_of_nonnormal_abelian
    (abelian : ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X)
      (L V : Subgroup X) (n : ℕ),
      HigherRankHypothesis KnownSimple.IsKnownSimple T L V n → n = 4 ∨ n = 5 →
      PreferredDimension KnownSimple.IsKnownSimple T n →
      EarlierSetupResults.{u} KnownSimple.IsKnownSimple →
      NaturalReduction KnownSimple.IsKnownSimple.{u} 4 →
      ∀ F : InvariantFlag T V n, ¬ ((F.Li L 1).subgroupOf F.H).Normal →
        IsMulCommutative F.U) :
    ComponentInput KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ T L V n h hn preferred earlier four F
  refine ⟨?_, Components.componentGeometry earlier h hn F⟩
  by_cases hnormal : ((F.Li L 1).subgroupOf F.H).Normal
  · exact Components.point_span_abelian_of_point_residual_normal h hn earlier F hnormal
  · exact abelian X T L V n h hn preferred earlier four F hnormal

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
