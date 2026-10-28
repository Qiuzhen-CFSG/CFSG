module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.Attractor

/-!
# The rational projective attractor with its exact open basin

This is the source-facing form of Borel IV, 13.8. Rationality supplies the
weight basis, and the fixed-locus finiteness forces the unique highest line.
The original projective orbit has a fixed attracting point in a projective
hyperplane complement. That complement intersects the orbit in precisely the
points whose cocharacter curves end at the attracting point. The converse
uses closed-set specialization of the invariant complementary hyperplane.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit

universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

theorem mem_hyperplaneOpen_of_cocharacter_limit
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (j : Fin (Module.finrank k E)) (x : Point (projectiveSpace k E))
    (f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E))
    (hcurve : ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
      A.toMulAction.smul
        (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) x)
    (hzero : (f (ProjectivePolynomialCurve.affinePoint 0)).1 (IsLocalRing.closedPoint k) ∈
      projectiveHyperplaneOpen b₀ (b.coord j)) :
    x.1 (IsLocalRing.closedPoint k) ∈ projectiveHyperplaneOpen b₀ (b.coord j) := by
  by_contra hx
  let U := projectiveHyperplaneOpen b₀ (b.coord j)
  have hzero' : (f (ProjectivePolynomialCurve.affinePoint 0)).1 (IsLocalRing.closedPoint k) ∉ U := by
    apply ProjectivePolynomialCurve.affinePoint_mem_of_nonzero
      (U.isOpen.isClosed_compl.preimage f.hom.continuous)
    intro a ha
    change (f (ProjectivePolynomialCurve.affinePoint a)).1 (IsLocalRing.closedPoint k) ∉ U
    rw [hcurve a ha]
    apply projectiveHyperplaneOpen_not_mem_of_map b₀ (b.coord j) _ _ x _ (he _ x) hx
    intro w hw
    have hw' : b.equivFun w j = 0 := hw
    change b.equivFun ((ρ.action (T.includePoint
      (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹)))).1 w) j = 0
    rw [torus_weight_basis_coordinates ρ T b χ hweight, hw', mul_zero]
  exact hzero' hzero

/-- The full original-action source endpoint: a fixed attracting point, an
open basin containing it, and actual affine curves characterizing that basin.
No diagonalization, limit, or highest-line premise remains. -/
theorem exists_attractor_of_finite_fixed_orbit
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (x : Point (projectiveSpace k E))
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (hfinite : (fixedOrbit A T c x).Finite) :
    ∃ (U : (projectiveSpace k E).toScheme.Opens) (y : Point (projectiveSpace k E)),
      y ∈ fixedOrbit A T c x ∧
      y.1 (IsLocalRing.closedPoint k) ∈ U ∧
      IsOpen {g : Variety.Point G | (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ U} ∧
      (∃ g : Variety.Point G, (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ U) ∧
      ∀ z : Point (projectiveSpace k E), (∃ g : Variety.Point G, A.toMulAction.smul g x = z) →
        (z.1 (IsLocalRing.closedPoint k) ∈ U ↔
          ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E),
            f (ProjectivePolynomialCurve.affinePoint 0) = y ∧
            ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
              A.toMulAction.smul
                (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) z) := by
  obtain ⟨b, χ, hweight⟩ := exists_finite_torus_weight_basis ρ hρ T hT
  obtain ⟨v, hv, rfl⟩ := exists_projective_vector b₀ x
  obtain ⟨M, j, y, _, _, hy, hyU, hopen, hne, hcurves, _⟩ :=
    exists_attractor_in_weight_basis ρ hρ hG T c A b₀ b χ he hweight v hv hclosed hfinite
  refine ⟨projectiveHyperplaneOpen b₀ (b.coord j), y, hy, hyU, hopen, hne, ?_⟩
  intro z hz
  obtain ⟨g, rfl⟩ := hz
  constructor
  · exact hcurves g
  · rintro ⟨f, hf, hcurve⟩
    apply mem_hyperplaneOpen_of_cocharacter_limit ρ T c A b₀ b χ he hweight j _ f hcurve
    rw [hf]
    exact hyU

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
