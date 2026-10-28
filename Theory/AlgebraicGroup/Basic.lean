module

public import Theory.AlgebraicGroup.Variety.Defs

universe u

/-! Core algebraic-group structure on an affine variety. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- An algebraic group is a group on the zero locus whose operations are given
by polynomial coordinate functions. -/
public class _root_.AlgebraicGroup (V : Variety k) extends Group (Variety.Point V) where
  mulPolynomial : V.Coordinates →
    MvPolynomial (V.Coordinates ⊕ V.Coordinates) k
  invPolynomial : V.Coordinates →
    MvPolynomial V.Coordinates k
  mul_regular : letI : Group (Variety.Point V) := toGroup
    ∀ (i : V.Coordinates) (x y : Variety.Point V), (x * y).val i =
      evalPolynomial (Sum.elim x.val y.val) (mulPolynomial i)
  inv_regular : letI : Group (Variety.Point V) := toGroup
    ∀ (i : V.Coordinates) (x : Variety.Point V),
      (x⁻¹).val i = evalPolynomial x.val (invPolynomial i)

public instance group (V : Variety k) [h : AlgebraicGroup V] :
    Group (Variety.Point V) := h.toGroup

end Theory.AlgebraicGroup
