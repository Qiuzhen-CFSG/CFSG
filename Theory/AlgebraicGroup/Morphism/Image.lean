module

public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Variety.Zariski

universe u

/-! Images of algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The abstract image subgroup of an algebraic-group morphism. -/
@[expose]
public def Morphism.image {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    Subgroup (Variety.Point H) := f.onPoints.range

public lemma Morphism.image_carrier {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    (f.image : Set (Variety.Point H)) = Set.range f.onPoints := by
  rfl

/-- The image clause is provable in the present affine presentation whenever
the source has finitely many rational points.  The unrestricted algebraic
image theorem requires the Chevalley/representation machinery not imported by
this foundational module. -/
public theorem Morphism.image_isZariskiClosed_of_finiteDomain
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    [Finite (Variety.Point G)] (f : AlgebraicGroup.Morphism G H) :
    IsZariskiClosed H (f.image : Set (Variety.Point H)) := by
  rw [f.image_carrier]
  exact isZariskiClosed_of_finite (Set.finite_range f.onPoints)

end Theory.AlgebraicGroup
