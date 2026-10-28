module

public import Theory.AlgebraicGroup.Variety.ProjectivePolynomialCurve
public import Theory.AlgebraicGroup.Variety.ClosedLocus

/-!
# Uniqueness and naturality of affine-curve endpoints

The equalizer of two maps to a separated variety is closed. Its inverse image
on the affine line contains zero if it contains every nonzero parameter. Thus
the explicit cocharacter curves have unique endpoints, and their endpoints
commute with every morphism. This is the embedding-independent comparison used
in Borel, IV, 13.3 and 13.11.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem point_mem_equalizerSupport_iff {V W : Geometric k}
    (f g : Morphism V W) (x : Point V) :
    x.1 (IsLocalRing.closedPoint k) ∈ equalizerSupport f g ↔ f x = g x := by
  rw [point_mem_reducedEqualizer_iff f g x]
  exact point_mem_reducedClosedSubvariety_iff V (equalizerSupport f g) x

/-- Maps to a separated variety agreeing away from zero have the same endpoint. -/
theorem endpoint_eq_of_nonzero {Y : Geometric k}
    (f g : Morphism (polynomialAffineLine k) Y)
    (h : ∀ a : k, a ≠ 0 → f (affinePoint a) = g (affinePoint a)) :
    f (affinePoint 0) = g (affinePoint 0) := by
  apply (point_mem_equalizerSupport_iff f g (affinePoint 0)).mp
  apply affinePoint_mem_of_nonzero (equalizerSupport f g).isClosed
  intro a ha
  exact (point_mem_equalizerSupport_iff f g (affinePoint a)).mpr (h a ha)

/-- Endpoint formation commutes with any geometric morphism, whenever the
nonzero parameter curves agree under that morphism. -/
theorem endpoint_natural {X Y : Geometric k} (φ : Morphism X Y)
    (f : Morphism (polynomialAffineLine k) X)
    (g : Morphism (polynomialAffineLine k) Y)
    (h : ∀ a : k, a ≠ 0 → φ (f (affinePoint a)) = g (affinePoint a)) :
    φ (f (affinePoint 0)) = g (affinePoint 0) := by
  exact endpoint_eq_of_nonzero (f.comp φ) g h

end Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
