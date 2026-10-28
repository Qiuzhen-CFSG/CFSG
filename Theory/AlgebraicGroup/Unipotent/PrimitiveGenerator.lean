module

public import Theory.AlgebraicGroup.Instance.Additive
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Variety.InjectiveOfPullbackSurjective

universe u

/-!
# Primitive additive generators

This module isolates the coordinate-algebra endpoint of the classification of
connected one-dimensional unipotent algebraic groups in GLS Proposition
1.3.5(c).  A primitive additive generator is a regular function `u` with
`u(x * y) = u(x) + u(y)` which generates the full polynomial-function algebra.

Evaluation of `u` defines a morphism to the additive group.  Generation makes
its pullback surjective, hence the morphism is injective on points.  If it is
also surjective on points, affine duality constructs the regular inverse and
therefore an algebraic-group isomorphism.  Thus the remaining classification
work is precisely the genuine primitive-generator existence theorem, without
asserting that an arbitrary finite-kernel additive character has a regular
section in positive characteristic.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A primitive additive coordinate which generates the polynomial-function
algebra of an algebraic group. -/
public structure PrimitiveAdditiveGeneratorData
    (Y : Variety k) [AlgebraicGroup Y] where
  coordinate : Variety.PolynomialFunction Y
  coordinate_one : coordinate (1 : Variety.Point Y) = 0
  coordinate_mul : ∀ x y : Variety.Point Y,
    coordinate (x * y) = coordinate x + coordinate y
  coordinate_nontrivial : ∃ y : Variety.Point Y, coordinate y ≠ 0
  generates : Algebra.adjoin k {coordinate} = ⊤

/-- The point of the additive group with affine coordinate `t`. -/
@[expose]
public def additiveGroupPoint (t : k) :
    Variety.Point (additiveGroupVariety k) :=
  (additiveGroupPointEquiv k).symm (Multiplicative.ofAdd t)

/-- Evaluation of a primitive additive generator as an algebraic-group
morphism to the additive group. -/
@[expose]
public def PrimitiveAdditiveGeneratorData.morphism
    {Y : Variety k} [AlgebraicGroup Y]
    (D : PrimitiveAdditiveGeneratorData Y) :
    AlgebraicGroup.Morphism Y (additiveGroupVariety k) where
  toVariety :=
    { toFun := fun y ↦ additiveGroupPoint (D.coordinate y)
      regular := by
        intro i
        obtain ⟨p, hp⟩ := D.coordinate.representedBy
        refine ⟨p, ?_⟩
        intro y
        rw [show i = PUnit.unit by rfl]
        change D.coordinate y = evalPolynomial y.val p
        exact hp y }
  map_one := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (D.coordinate 1) = Multiplicative.ofAdd 0
    rw [D.coordinate_one]
  map_mul := by
    intro x y
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (D.coordinate (x * y)) =
      Multiplicative.ofAdd (D.coordinate x + D.coordinate y)
    rw [D.coordinate_mul]

/-- The affine coordinate function on the additive group. -/
public noncomputable def additiveGroupCoordinate :
    Variety.PolynomialFunction (additiveGroupVariety k) :=
  Variety.PolynomialFunction.ofPolynomial
    (additiveGroupVariety k) (MvPolynomial.X PUnit.unit)

/-- Pulling the affine coordinate back along the morphism defined by a
primitive generator recovers that generator. -/
public lemma PrimitiveAdditiveGeneratorData.morphism_pullback_additiveGroupCoordinate
    {Y : Variety k} [AlgebraicGroup Y]
    (D : PrimitiveAdditiveGeneratorData Y) :
    D.morphism.toVariety.pullbackAlgHom additiveGroupCoordinate = D.coordinate := by
  apply Variety.PolynomialFunction.ext
  intro y
  change evalPolynomial (additiveGroupPoint (D.coordinate y)).val
      (MvPolynomial.X PUnit.unit) = D.coordinate y
  rw [evalPolynomial_X]
  rfl

/-- A primitive algebra generator makes the induced coordinate pullback
surjective. -/
public theorem PrimitiveAdditiveGeneratorData.morphism_pullback_surjective
    {Y : Variety k} [AlgebraicGroup Y]
    (D : PrimitiveAdditiveGeneratorData Y) :
    Function.Surjective D.morphism.toVariety.pullbackRingHom := by
  apply (AlgHom.range_eq_top D.morphism.toVariety.pullbackAlgHom).mp
  apply top_unique
  rw [← D.generates]
  apply Algebra.adjoin_le
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst q
  exact ⟨additiveGroupCoordinate,
    D.morphism_pullback_additiveGroupCoordinate⟩

/-- A point-surjective primitive-generator morphism is an isomorphism from the
additive group. -/
public theorem PrimitiveAdditiveGeneratorData.additiveGroupIso_of_surjective
    {Y : Variety k} [AlgebraicGroup Y]
    (D : PrimitiveAdditiveGeneratorData Y)
    (hsurjective : Function.Surjective D.morphism.onPoints) :
    Nonempty (AlgebraicGroup.Iso (additiveGroupVariety k) Y) := by
  have hpull := D.morphism_pullback_surjective
  have hinjective : Function.Injective D.morphism.onPoints :=
    D.morphism.toVariety.injective_of_pullbackRingHom_surjective hpull
  obtain ⟨e, -⟩ :=
    algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
      D.morphism ⟨hinjective, hsurjective⟩ hpull
  exact ⟨e.symm⟩

end Theory.AlgebraicGroup
