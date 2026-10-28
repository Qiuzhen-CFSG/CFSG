module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The coordinate definition of a rational representation's differential is
independent of the chosen basis and representing general-linear morphism. -/
public theorem rationalRepresentationDifferential_eq_of_point_action
    (ρ : RationalRepresentation G V)
    (e b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f q : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (hq : ∀ g, glPointEquivOf k V b (q.onPoints g) = ρ.action g) :
    rationalRepresentationDifferential ρ e f =
      rationalRepresentationDifferential ρ b q := by
  ext D v
  apply b.ext_elem
  intro i
  change b.coord i ((rationalRepresentationDifferential ρ e f) D v) =
    b.coord i ((rationalRepresentationDifferential ρ b q) D v)
  rw [rationalRepresentationDifferential_linearMatrixCoefficient,
    rationalRepresentationDifferential_linearMatrixCoefficient]
  congr 1
  apply Variety.PolynomialFunction.ext
  intro g
  rw [rationalRepresentationLinearMatrixCoefficient_apply ρ e f hf]
  rw [rationalRepresentationLinearMatrixCoefficient_apply ρ b q hq]

end Theory.AlgebraicGroup.Bor1
