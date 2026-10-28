module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.ProjectiveCharts
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Density of the two reciprocal parametrizations

A closed subset containing all nonzero rational values of an affine curve
contains its entire scheme image. Hence either of two reciprocal affine
parametrizations is dominant as soon as the other is. This connects both
normal charts to the same actual projective curve in Borel §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem affine_curve_range_subset_closed_of_nonzero
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism (polynomialAffineLine k) Y)
    {Z : Set Y.toScheme} (hZ : IsClosed Z)
    (h : ∀ a : k, a ≠ 0 → (f (affinePoint a)).1 (IsLocalRing.closedPoint k) ∈ Z) :
    Set.range f.hom ⊆ Z := by
  have hall (a : k) : (f (affinePoint a)).1 (IsLocalRing.closedPoint k) ∈ Z :=
    affinePoint_mem_of_nonzero (hZ.preimage f.hom.continuous) h a
  have hclosed : IsClosed (f.hom ⁻¹' Z) := hZ.preimage f.hom.continuous
  have hpoints : closedPoints (polynomialAffineLine k).toScheme ⊆ f.hom ⁻¹' Z := by
    intro z hz
    let p : Point (polynomialAffineLine k) :=
      (pointEquivClosedPoint (polynomialAffineLine k).structureMap).symm ⟨z, hz⟩
    obtain ⟨a, ha⟩ := affinePoint_surjective p
    have hpa : (affinePoint a).1 (IsLocalRing.closedPoint k) = z := by
      rw [ha]
      exact congrArg Subtype.val
        ((pointEquivClosedPoint (polynomialAffineLine k).structureMap).apply_symm_apply ⟨z, hz⟩)
    have hh := hall a
    change f.hom ((affinePoint a).1 (IsLocalRing.closedPoint k)) ∈ Z at hh
    rwa [hpa] at hh
  have : JacobsonSpace (polynomialAffineLine k).toScheme :=
    LocallyOfFiniteType.jacobsonSpace (polynomialAffineLine k).structureMap
  have hfull : Set.univ ⊆ f.hom ⁻¹' Z := by
    rw [← closure_closedPoints]
    exact hclosed.closure_subset_iff.mpr hpoints
  rintro _ ⟨x, rfl⟩
  exact hfull (Set.mem_univ x)

theorem reciprocal_curve_dominant
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f g : Morphism (polynomialAffineLine k) Y) [IsDominant f.hom]
    (h : ∀ a : k, a ≠ 0 → f (affinePoint a) = g (affinePoint a⁻¹)) :
    IsDominant g.hom := by
  have hsub : Set.range f.hom ⊆ closure (Set.range g.hom) :=
    affine_curve_range_subset_closed_of_nonzero f isClosed_closure (by
      intro a ha
      rw [h a ha]
      exact subset_closure ⟨(affinePoint a⁻¹).1 (IsLocalRing.closedPoint k), rfl⟩)
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff]
  rw [← f.hom.denseRange.closure_range]
  exact closure_minimal hsub isClosed_closure

end Theory.AlgebraicGroup.Bor1.FlagCurve
