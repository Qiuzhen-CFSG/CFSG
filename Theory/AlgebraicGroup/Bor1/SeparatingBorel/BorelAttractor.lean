module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.AttractorComparison
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.SourceAttractor

/-!
# The Borel defined by a semiregular cocharacter

The closed original Borel orbit has finitely many cocharacter-fixed points.
The rational projective attractor theorem constructs an actual fixed endpoint
and its open basin. Its stabilizer is a Borel containing the maximal torus.
No limit-description or highest-weight certificate is assumed.

Source: Borel, *Linear Algebraic Groups*, IV, 13.8--13.10.
-/

public section
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

theorem exists_borel_attractor
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (A : MorphicAction G (projectiveSpace k E))
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (x : Point (projectiveSpace k E))
    (hx : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer) :
    ∃ (U : (projectiveSpace k E).toScheme.Opens) (y : Point (projectiveSpace k E)),
      (∃ g : Variety.Point G, A.toMulAction.smul g x = y) ∧
      IsBorelSubgroup (A.pointStabilizer y) ∧ T ≤ A.pointStabilizer y ∧
      y.1 (IsLocalRing.closedPoint k) ∈ U ∧
      ∀ z : Point (projectiveSpace k E), (∃ g : Variety.Point G, A.toMulAction.smul g x = z) →
        (z.1 (IsLocalRing.closedPoint k) ∈ U ↔
          ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E),
            f (ProjectivePolynomialCurve.affinePoint 0) = y ∧
            ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
              A.toMulAction.smul
                (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) z) := by
  let := A.toMulAction
  have hclosed := A.orbit_isClosed_of_borel_fixed hG B hB x (fun g hg => (hx g).mpr hg)
  have hfinite : (fixedOrbit A T c x).Finite :=
    finite_fixed_orbit_of_semiregular_cocharacter hG B hB x hx T hT c hc
  obtain ⟨U,y,hy,hyU,_,_,hcurve⟩ :=
    exists_attractor_of_finite_fixed_orbit ρ hρ hG T hT.1 c A b he x hclosed hfinite
  have hb := isBorel_pointStabilizer_containing_torus hG B hB A x hx T hT c hc y hy.1 hy.2
  exact ⟨U,y,hy.1,hb.1,hb.2,hyU,hcurve⟩
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
