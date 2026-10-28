module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential
public import Theory.AlgebraicGroup.Representations.Operations

universe u v w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]
variable {W : Type w} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

/-- A pointwise intertwining linear map also intertwines the coordinate
differentials at the identity. -/
public theorem rationalRepresentationDifferential_intertwines
    (ρ : RationalRepresentation G V) (σ : RationalRepresentation G W)
    (L : V →ₗ[k] W) (hL : Intertwines ρ σ L)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g)
    (e : Module.Basis (Fin (Module.finrank k W)) k W)
    (q : AlgebraicGroup.Morphism G (glVarietyOf k W))
    (hq : ∀ g, glPointEquivOf k W e (q.onPoints g) = σ.action g)
    (D : IdentityPointDerivation G) (v : V) :
    L (rationalRepresentationDifferential ρ b f D v) =
      rationalRepresentationDifferential σ e q D (L v) := by
  apply e.ext_elem
  intro i
  change e.coord i
      (L (rationalRepresentationDifferential ρ b f D v)) = _
  change (e.coord i).comp L
      (rationalRepresentationDifferential ρ b f D v) = _
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  change _ = e.coord i
    (rationalRepresentationDifferential σ e q D (L v))
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  congr 1
  apply Variety.PolynomialFunction.ext
  intro g
  rw [rationalRepresentationLinearMatrixCoefficient_apply ρ b f hf]
  rw [rationalRepresentationLinearMatrixCoefficient_apply σ e q hq]
  exact congrArg (e.coord i) (hL g v)

end Theory.AlgebraicGroup.Bor1
