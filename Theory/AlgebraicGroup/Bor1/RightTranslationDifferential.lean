module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The infinitesimal right-translation action on Chevalley's finite
coordinate-function space. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpanDifferential
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    IdentityPointDerivation G →ₗ[k]
      Module.End k H.rightTranslateVanishingSpan :=
  rationalRepresentationDifferential
    (⟨H.rightTranslateVanishingSpanGeneralLinear⟩ :
      RationalRepresentation G H.rightTranslateVanishingSpan)
    H.rightTranslateVanishingSpanBasis
    (H.rightTranslateVanishingRepresentationMorphismOfBasis
      H.rightTranslateVanishingSpanBasis)

/-- Evaluating the infinitesimal translate of `q` at the identity recovers
the tangent derivation applied to `q`. -/
public theorem ClosedSubgroup.rightTranslateVanishingSpanDifferential_eval_one
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (D : IdentityPointDerivation G) (q : H.rightTranslateVanishingSpan) :
    (ClosedSubgroup.rightTranslateVanishingSpanDifferential H D q).1 1 =
      D q.1 := by
  change (polynomialFunctionSubspaceEvaluation G
      H.rightTranslateVanishingSpan 1)
      (ClosedSubgroup.rightTranslateVanishingSpanDifferential H D q) = D q.1
  rw [ClosedSubgroup.rightTranslateVanishingSpanDifferential,
    rationalRepresentationDifferential_linearMatrixCoefficient]
  rw [H.rightTranslateVanishingSpan_eq_linearMatrixCoefficient
    H.rightTranslateVanishingSpanBasis q]

end Theory.AlgebraicGroup.Bor1
