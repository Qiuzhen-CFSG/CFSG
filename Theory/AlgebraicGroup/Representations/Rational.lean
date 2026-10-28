module

public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Morphism.Basic

universe u v

/-! Rational finite-dimensional representations of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A linear action of the rational-point group.  Rationality is recorded by
`IsRationalRepresentation`. -/
public structure RationalRepresentation
    (G : Variety k) [AlgebraicGroup G] (V : Type v)
    [AddCommGroup V] [Module k V] where
  action : Variety.Point G →* LinearMap.GeneralLinearGroup k V

variable [IsAlgClosed k]

/-- A linear action is rational when it is induced by an algebraic-group
morphism to a general linear group in some basis. -/
@[expose]
public def IsRationalRepresentation
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V] (ρ : RationalRepresentation G V) : Prop :=
  ∃ e : Module.Basis (Fin (Module.finrank k V)) k V,
    ∃ f : AlgebraicGroup.Morphism G (glVarietyOf k V),
      ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g

/-- A submodule preserved by every operator of a rational representation. -/
@[expose]
public def IsInvariantSubmodule
    {G : Variety k} [AlgebraicGroup G] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation G V) (W : Submodule k V) : Prop :=
  ∀ g v, v ∈ W → (ρ.action g : Module.End k V) v ∈ W

end Theory.AlgebraicGroup
