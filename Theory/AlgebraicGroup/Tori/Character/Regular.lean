module

public import Theory.AlgebraicGroup.Tori.Character.Point

universe u

/-! Polynomial functions underlying algebraic characters. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Pull back the unique positive diagonal coordinate of `KMult` along a
character. -/
@[expose]
public noncomputable def TorusCharacter.scalarPolynomialFunction
    {T : Variety k} [AlgebraicGroup T] (χ : TorusCharacter T) :
    Variety.PolynomialFunction T :=
  Variety.PolynomialFunction.pullback χ.toVariety
    (Variety.PolynomialFunction.ofPolynomial (KMult k)
      (MvPolynomial.X (Sum.inl (ULift.up (0 : Fin 1)))))

/-- Evaluation of the scalar regular function agrees with the scalar point
character. -/
public lemma TorusCharacter.scalarPolynomialFunction_apply
    {T : Variety k} [AlgebraicGroup T] (χ : TorusCharacter T)
    (x : Variety.Point T) :
    χ.scalarPolynomialFunction x = (χ.pointCharacter x : k) := by
  rw [TorusCharacter.scalarPolynomialFunction]
  simp [Variety.PolynomialFunction.pullback,
    Variety.PolynomialFunction.toFun,
    Variety.PolynomialFunction.ofPolynomial,
    evalPolynomial,
    TorusCharacter.pointCharacter,
    Theory.AlgebraicGroup.Morphism.onPoints,
    dPointEquiv,
    dPointEntry]

end Theory.AlgebraicGroup
