module

public import Theory.AlgebraicGroup.Tori.Character.Defs
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore

/-!
Contraction by an algebraic cocharacter.

We use the inverse-conjugation convention of GLS3, Definition 1.9.1. An
algebraic curve extends this conjugation orbit to the affine line and takes
value one at zero. Multiplying and inverting the curves shows that the
contracted elements form a subgroup. This is the geometric condition used in
the positive-root construction of Borel, §14.5, and GLS3, Theorem 1.11.2.
No assertion that contracted elements are unipotent is part of the definition.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Inverse conjugation by a cocharacter extends to the affine line with value
one at zero. The extension is an algebraic variety morphism. -/
@[expose]
public def IsCocharacterContracted
    (lambda : AlgebraicGroup.Morphism (KMult k) G)
    (g : Variety.Point G) : Prop :=
  ∃ f : Variety.Morphism (KPlus k) G,
    f.toFun (kPlusPoint 0) = 1 ∧
      ∀ t : Variety.Point (KMult k),
        f.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) =
          (lambda.onPoints t)⁻¹ * g * lambda.onPoints t

public theorem IsCocharacterContracted.one
    (lambda : AlgebraicGroup.Morphism (KMult k) G) :
    IsCocharacterContracted lambda 1 := by
  refine ⟨Variety.Morphism.const _ _ 1, rfl, ?_⟩
  intro t
  change 1 = (lambda.onPoints t)⁻¹ * 1 * lambda.onPoints t
  simp

public theorem IsCocharacterContracted.mul
    {lambda : AlgebraicGroup.Morphism (KMult k) G}
    {g h : Variety.Point G} (hg : IsCocharacterContracted lambda g)
    (hh : IsCocharacterContracted lambda h) :
    IsCocharacterContracted lambda (g * h) := by
  obtain ⟨f, hf0, hf⟩ := hg
  obtain ⟨q, hq0, hq⟩ := hh
  refine ⟨(AlgebraicGroup.mulMorphism G).comp (f.pair q), ?_, ?_⟩
  · change f.toFun (kPlusPoint 0) * q.toFun (kPlusPoint 0) = 1
    rw [hf0, hq0, one_mul]
  · intro t
    change f.toFun (kPlusPoint _) * q.toFun (kPlusPoint _) = _
    rw [hf, hq]
    simp [mul_assoc]

public theorem IsCocharacterContracted.inv
    {lambda : AlgebraicGroup.Morphism (KMult k) G}
    {g : Variety.Point G} (hg : IsCocharacterContracted lambda g) :
    IsCocharacterContracted lambda g⁻¹ := by
  obtain ⟨f, hf0, hf⟩ := hg
  refine ⟨(AlgebraicGroup.invMorphism G).comp f, ?_, ?_⟩
  · change (f.toFun (kPlusPoint 0))⁻¹ = 1
    rw [hf0, inv_one]
  · intro t
    change (f.toFun (kPlusPoint _))⁻¹ = _
    rw [hf]
    simp [mul_assoc]

/-- The extension at the scalar one recovers the contracted element. -/
public theorem IsCocharacterContracted.exists_curve
    {lambda : AlgebraicGroup.Morphism (KMult k) G}
    {g : Variety.Point G} (hg : IsCocharacterContracted lambda g) :
    ∃ f : Variety.Morphism (KPlus k) G,
      f.toFun (kPlusPoint 0) = 1 ∧ f.toFun (kPlusPoint 1) = g ∧
        ∀ t : Variety.Point (KMult k),
          f.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) =
            (lambda.onPoints t)⁻¹ * g * lambda.onPoints t := by
  obtain ⟨f, hf0, hf⟩ := hg
  refine ⟨f, hf0, ?_, hf⟩
  simpa [dPointEquiv_one] using hf 1

end Theory.AlgebraicGroup
