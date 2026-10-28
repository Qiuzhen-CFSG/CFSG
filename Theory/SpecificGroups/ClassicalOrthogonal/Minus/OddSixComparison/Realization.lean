module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Exterior realizations on the original minus-six quadratic space

This interface specifies a coefficient embedding, six bivector coordinates
spanning after scalar extension, and an isometric action intertwined with the
literal compound matrices of SU₄. In particular, the orthogonal carrier is
always the full isometry group of the independently chosen minus form.

No image, commutator membership, surjectivity or projective comparison is
part of the data. Those are separate group-theoretic obligations. The
coordinates retain the quadratic values, so that a producer must establish
both the odd-characteristic descent and transport of the anisotropic plane.
Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors

variable (F E : Type) [Field F] [Finite F] [Field E]

/-- The original full minus-six isometry group, before taking commutators. -/
abbrev FullOrthogonal := Orthogonal F (Space F 2) (quadraticForm F 3)

/-- Geometric realization of the genuine unitary exterior square on the
original minus-six form. Image theorems are deliberately separate. -/
structure ExteriorRealization (J : HermitianForm 4 E) where
  coefficient : F →+* E
  coordinates : Space F 2 →ₛₗ[coefficient] Six E
  coordinates_injective : Function.Injective coordinates
  coordinates_span : Submodule.span E (Set.range coordinates) = ⊤
  quadratic : ∀ v, pfaffian (coordinates v) = coefficient (quadraticForm F 3 v)
  action : J.specialSubgroup →* FullOrthogonal F
  intertwines : ∀ g v, coordinates ((action g).val v) = exteriorMap g.val.val (coordinates v)

variable {F E} {J : HermitianForm 4 E} (R : ExteriorRealization F E J)

/-- Equality on descended vectors determines the full exterior linear map. -/
theorem ExteriorRealization.bivector_ext
    {L M : Six E →ₗ[E] Six E}
    (h : ∀ v, L (R.coordinates v) = M (R.coordinates v)) : L = M :=
  LinearMap.ext_on_range R.coordinates_span h

/-- Scalar action on the original space is equivalent to scalar exterior action,
with the original coefficient embedding retained. -/
theorem ExteriorRealization.scalar_action_iff (g : J.specialSubgroup) (c : F) :
    (∀ v, (R.action g).val v = c • v) ↔
      (∀ w, exteriorMap g.val.val w = R.coefficient c • w) := by
  constructor
  · intro h
    have he : exteriorMap g.val.val = R.coefficient c • LinearMap.id := by
      apply R.bivector_ext
      intro v
      rw [← R.intertwines, h, R.coordinates.map_smulₛₗ]
      rfl
    intro w
    rw [he]
    rfl
  · intro h v
    apply R.coordinates_injective
    rw [R.intertwines, h, R.coordinates.map_smulₛₗ]

end ClassicalOrthogonal.Minus.OddSixComparison
