module

public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Characters and cocharacters of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A character is an algebraic-group morphism to the multiplicative group. -/
public abbrev TorusCharacter (T : Variety k) [AlgebraicGroup T] :=
  AlgebraicGroup.Morphism T (KMult k)

/-- A cocharacter is an algebraic-group morphism from the multiplicative
group. -/
public abbrev TorusCocharacter (T : Variety k) [AlgebraicGroup T] :=
  AlgebraicGroup.Morphism (KMult k) T

end Theory.AlgebraicGroup
