module

public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.Variety.Morphism

universe u

/-! Regular multiplication, inversion, translation, and conjugation maps. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Multiplication as a polynomial morphism of varieties. -/
@[expose]
public def mulMorphism (G : Variety k) [hG : AlgebraicGroup G] :
    Variety.Morphism (Variety.prod G G) G where
  toFun := fun x ↦
    (Variety.prodPointEquiv G G x).1 * (Variety.prodPointEquiv G G x).2
  regular := fun i ↦ ⟨hG.mulPolynomial i, fun x ↦ by
    rw [hG.mul_regular]
    congr 1
    funext j
    cases j <;> rfl⟩

/-- Inversion as a polynomial morphism of varieties. -/
@[expose]
public def invMorphism (G : Variety k) [hG : AlgebraicGroup G] :
    Variety.Morphism G G where
  toFun := fun x ↦ x⁻¹
  regular := fun i ↦ ⟨hG.invPolynomial i, hG.inv_regular i⟩

/-- Left translation by a fixed point is polynomial. -/
@[expose]
public def leftMulMorphism (G : Variety k) [AlgebraicGroup G]
    (a : Variety.Point G) : Variety.Morphism G G :=
  (Theory.AlgebraicGroup.mulMorphism G).comp
    ((Variety.Morphism.const G G a).pair (Variety.Morphism.id G))

/-- Right translation by a fixed point is polynomial. -/
@[expose]
public def rightMulMorphism (G : Variety k) [AlgebraicGroup G]
    (a : Variety.Point G) : Variety.Morphism G G :=
  (Theory.AlgebraicGroup.mulMorphism G).comp
    ((Variety.Morphism.id G).pair (Variety.Morphism.const G G a))

/-- Conjugation by a fixed point is polynomial. -/
@[expose]
public def conjugationByMorphism
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    Variety.Morphism G G :=
  (Theory.AlgebraicGroup.rightMulMorphism G g⁻¹).comp
    (Theory.AlgebraicGroup.leftMulMorphism G g)

/-- Conjugating a fixed point by the variable point is polynomial. -/
@[expose]
public def conjugateMorphism (G : Variety k) [AlgebraicGroup G]
    (a : Variety.Point G) : Variety.Morphism G G :=
  (Theory.AlgebraicGroup.mulMorphism G).comp
    ((Theory.AlgebraicGroup.rightMulMorphism G a).pair
      (Theory.AlgebraicGroup.invMorphism G))

/-- Conjugating a fixed point by the inverse of the variable point is
polynomial. -/
@[expose]
public def inverseConjugateMorphism (G : Variety k)
    [AlgebraicGroup G] (a : Variety.Point G) : Variety.Morphism G G :=
  (Theory.AlgebraicGroup.conjugateMorphism G a).comp
    (Theory.AlgebraicGroup.invMorphism G)

public lemma leftMulMorphism_apply (G : Variety k)
    [AlgebraicGroup G] (a x : Variety.Point G) :
    (Theory.AlgebraicGroup.leftMulMorphism G a).toFun x = a * x := by
  simp [Theory.AlgebraicGroup.leftMulMorphism, Theory.AlgebraicGroup.mulMorphism,
    Variety.Morphism.comp, Variety.Morphism.pair, Variety.Morphism.const,
    Variety.Morphism.id, Variety.prodPointEquiv]

public lemma rightMulMorphism_apply (G : Variety k)
    [AlgebraicGroup G] (a x : Variety.Point G) :
    (Theory.AlgebraicGroup.rightMulMorphism G a).toFun x = x * a := by
  simp [Theory.AlgebraicGroup.rightMulMorphism, Theory.AlgebraicGroup.mulMorphism,
    Variety.Morphism.comp, Variety.Morphism.pair, Variety.Morphism.const,
    Variety.Morphism.id, Variety.prodPointEquiv]

public lemma conjugationByMorphism_apply
    (G : Variety k) [AlgebraicGroup G] (g x : Variety.Point G) :
    (Theory.AlgebraicGroup.conjugationByMorphism G g).toFun x =
      g * x * g⁻¹ := by
  simp [Theory.AlgebraicGroup.conjugationByMorphism,
    Theory.AlgebraicGroup.leftMulMorphism_apply,
    Theory.AlgebraicGroup.rightMulMorphism_apply, Variety.Morphism.comp]

public lemma conjugateMorphism_apply (G : Variety k)
    [AlgebraicGroup G] (a x : Variety.Point G) :
    (Theory.AlgebraicGroup.conjugateMorphism G a).toFun x = x * a * x⁻¹ := by
  simp [Theory.AlgebraicGroup.conjugateMorphism, Theory.AlgebraicGroup.mulMorphism,
    Theory.AlgebraicGroup.rightMulMorphism_apply, Theory.AlgebraicGroup.invMorphism,
    Variety.Morphism.comp,
    Variety.Morphism.pair, Variety.prodPointEquiv]

public lemma inverseConjugateMorphism_apply (G : Variety k)
    [AlgebraicGroup G] (a x : Variety.Point G) :
    (Theory.AlgebraicGroup.inverseConjugateMorphism G a).toFun x = x⁻¹ * a * x := by
  simp [Theory.AlgebraicGroup.inverseConjugateMorphism, Variety.Morphism.comp,
    Theory.AlgebraicGroup.conjugateMorphism_apply, Theory.AlgebraicGroup.invMorphism]

/-! The algebraic commutator map. -/

/-- The two-variable regular map `(x,y) ↦ x y x⁻¹ y⁻¹`. -/
@[expose]
public def commutatorMorphism
    (G : Variety k) [AlgebraicGroup G] :
    Variety.Morphism (Variety.prod G G) G := by
  let fst := Variety.Morphism.fst G G
  let snd := Variety.Morphism.snd G G
  let xy := (AlgebraicGroup.mulMorphism G).comp (fst.pair snd)
  let xinv := (AlgebraicGroup.invMorphism G).comp fst
  let xyxinv := (AlgebraicGroup.mulMorphism G).comp (xy.pair xinv)
  let yinv := (AlgebraicGroup.invMorphism G).comp snd
  exact (AlgebraicGroup.mulMorphism G).comp (xyxinv.pair yinv)

/-- Pointwise evaluation of the algebraic commutator map. -/
public lemma commutatorMorphism_apply
    (G : Variety k) [AlgebraicGroup G]
    (x y : Variety.Point G) :
    (AlgebraicGroup.commutatorMorphism G).toFun
      ((Variety.prodPointEquiv G G).symm (x, y)) =
      x * y * x⁻¹ * y⁻¹ := by
  simp [AlgebraicGroup.commutatorMorphism, AlgebraicGroup.mulMorphism,
    AlgebraicGroup.invMorphism, Variety.Morphism.comp,
    Variety.Morphism.pair, Variety.Morphism.fst, Variety.Morphism.snd,
    Variety.prodPointEquiv]

end Theory.AlgebraicGroup
