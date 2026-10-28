module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Theory.AlgebraicGroup.Variety.CoordinateRing

universe u

/-! Geometric dimension of presented affine varieties. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The dimension of a single irreducible component of a presented variety:
the transcendence degree over `k` of the fraction field of its coordinate
ring (the component is a closed subvariety, and being irreducible its
coordinate ring is a domain). -/
@[expose]
public noncomputable def Variety.componentDimension (V : Variety k)
    (C : Set (Variety.Point V)) (hC : C ∈ irreducibleComponents (Variety.Point V)) : Cardinal :=
  Algebra.trdeg k (FractionRing (coordinateRing (Variety.closedSubvariety
    (Variety.isClosed_iff_isZariskiClosed.mp (isClosed_of_mem_irreducibleComponents C hC)))))

/-- Definition 1.1.5: the geometric dimension of a presented variety is the
maximum of the dimensions of its irreducible components.  For a connected
(irreducible) algebraic group this is the transcendence degree of the fraction
field of its coordinate ring; for a non-connected group all components are
cosets of the identity component and have the same dimension, so the maximum
is `dim K°`, matching the book's convention `dim K = dim K°`. -/
@[expose]
public noncomputable def Variety.dimension (V : Variety k) : Cardinal :=
  ⨆ C : {C : Set (Variety.Point V) // C ∈ irreducibleComponents (Variety.Point V)},
    Variety.componentDimension V C.1 C.2

end Theory.AlgebraicGroup
