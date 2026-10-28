module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.SourceCurves

/-!
# Actual rational-action limits in closed invariant sets

Rationality supplies a genuine torus weight basis. Choosing the largest occupied
cocharacter weight and applying the explicit polynomial curve proves that every
point of a closed invariant projective subset has a fixed endpoint there.
The original projective action and its basis are retained. In particular this
applies to each closed centralizer suborbit in Borel IV, 13.11.
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

/-- The source cocharacter limit, from rationality and an actual closed
invariant subset, with its full original-action affine curve. -/
theorem exists_cocharacter_limit_in_closed_invariant
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    {Z : Set (projectiveSpace k E).toScheme} (hZ : IsClosed Z)
    (hinv : ∀ (t : Variety.Point (KMult k)) (p : Point (projectiveSpace k E)),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
        (A.toMulAction.smul (T.includePoint (c.onPoints t)) p).1 (IsLocalRing.closedPoint k) ∈ Z)
    (x : Point (projectiveSpace k E)) (hx : x.1 (IsLocalRing.closedPoint k) ∈ Z) :
    ∃ (f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E))
      (y : Point (projectiveSpace k E)),
      f (ProjectivePolynomialCurve.affinePoint 0) = y ∧
      (∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
        A.toMulAction.smul
          (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) x) ∧
      y.1 (IsLocalRing.closedPoint k) ∈ Z ∧
      ∀ t : Variety.Point (KMult k), A.toMulAction.smul (T.includePoint (c.onPoints t)) y = y := by
  obtain ⟨b, χ, hweight⟩ := exists_finite_torus_weight_basis ρ hρ T hT
  obtain ⟨v, hv, rfl⟩ := exists_projective_vector b₀ x
  let m := fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))
  obtain ⟨M, h, hM⟩ := exists_largest_occupied_weight b m v hv
  refine ⟨originalTopCurve b₀ b m M v h,
    projectivePointOfVector (b₀.equivFun (topVector b m M v))
      (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b m M v h)),
    originalTopCurve_zero b₀ b m M v h hM, ?_, ?_, ?_⟩
  · intro a ha
    exact originalTopCurve_nonzero ρ T c A b₀ b χ he hweight M v hv h hM a ha
  · exact topVector_mem_closed_invariant ρ T c A b₀ b χ he hweight M v hv h hM hZ hinv hx
  · exact topVector_projective_fixed ρ T c A b₀ b χ he hweight M v h

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
