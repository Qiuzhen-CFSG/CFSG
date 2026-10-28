module

public import Theory.AlgebraicGroup.Morphism.Basic

universe u

/-! Direct products of algebraic groups and their universal morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The direct product algebraic group. -/
public noncomputable instance prod (G H : Variety k)
    [hG : AlgebraicGroup G] [hH : AlgebraicGroup H] :
    AlgebraicGroup (Variety.prod G H) := by
  let e := Variety.prodPointEquiv G H
  let hGroup : Group (Variety.Point (Variety.prod G H)) := e.group
  letI : Group (Variety.Point (Variety.prod G H)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := fun
        | Sum.inl i => MvPolynomial.rename (Sum.map Sum.inl Sum.inl)
            (hG.mulPolynomial i)
        | Sum.inr i => MvPolynomial.rename (Sum.map Sum.inr Sum.inr)
            (hH.mulPolynomial i)
      invPolynomial := fun
        | Sum.inl i => MvPolynomial.rename Sum.inl (hG.invPolynomial i)
        | Sum.inr i => MvPolynomial.rename Sum.inr (hH.invPolynomial i)
      mul_regular := by
        intro i x y
        have hmul : e (x * y) = e x * e y := rfl
        cases i with
        | inl i =>
            change (e (x * y)).1.val i =
              evalPolynomial (Sum.elim x.val y.val)
                (MvPolynomial.rename (Sum.map Sum.inl Sum.inl)
                  (hG.mulPolynomial i))
            rw [hmul, evalPolynomial_rename]
            have hcoordinates :
                (Sum.elim x.val y.val) ∘ Sum.map Sum.inl Sum.inl =
                  Sum.elim (e x).1.val (e y).1.val := by
              funext z
              cases z <;> rfl
            rw [hcoordinates]
            exact hG.mul_regular i (e x).1 (e y).1
        | inr i =>
            change (e (x * y)).2.val i =
              evalPolynomial (Sum.elim x.val y.val)
                (MvPolynomial.rename (Sum.map Sum.inr Sum.inr)
                  (hH.mulPolynomial i))
            rw [hmul, evalPolynomial_rename]
            have hcoordinates :
                (Sum.elim x.val y.val) ∘ Sum.map Sum.inr Sum.inr =
                  Sum.elim (e x).2.val (e y).2.val := by
              funext z
              cases z <;> rfl
            rw [hcoordinates]
            exact hH.mul_regular i (e x).2 (e y).2
      inv_regular := by
        intro i x
        have hinv : e x⁻¹ = (e x)⁻¹ := rfl
        cases i with
        | inl i =>
            change (e x⁻¹).1.val i = evalPolynomial x.val
              (MvPolynomial.rename Sum.inl (hG.invPolynomial i))
            rw [hinv, evalPolynomial_rename]
            have hcoordinates : x.val ∘ Sum.inl = (e x).1.val := by
              rfl
            rw [hcoordinates]
            exact hG.inv_regular i (e x).1
        | inr i =>
            change (e x⁻¹).2.val i = evalPolynomial x.val
              (MvPolynomial.rename Sum.inr (hH.invPolynomial i))
            rw [hinv, evalPolynomial_rename]
            have hcoordinates : x.val ∘ Sum.inr = (e x).2.val := by
              rfl
            rw [hcoordinates]
            exact hH.inv_regular i (e x).2 }

/-- The point equivalence for a direct product preserves multiplication. -/
public lemma Variety.prodPointEquiv_mul (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H]
    (x y : Variety.Point (Variety.prod G H)) :
    Variety.prodPointEquiv G H (x * y) =
      Variety.prodPointEquiv G H x * Variety.prodPointEquiv G H y := by
  rfl

/-- First projection from a direct product. -/
@[expose]
public def Morphism.fst (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Theory.AlgebraicGroup.Morphism (Variety.prod G H) G where
  toVariety :=
    { toFun := fun x ↦ (Variety.prodPointEquiv G H x).1
      regular := fun i ↦ ⟨MvPolynomial.X (Sum.inl i), fun x ↦ by
        simp [evalPolynomial, Variety.prodPointEquiv]⟩ }
  map_one := rfl
  map_mul := by intro x y; rfl

/-- Second projection from a direct product. -/
@[expose]
public def Morphism.snd (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Theory.AlgebraicGroup.Morphism (Variety.prod G H) H where
  toVariety :=
    { toFun := fun x ↦ (Variety.prodPointEquiv G H x).2
      regular := fun i ↦ ⟨MvPolynomial.X (Sum.inr i), fun x ↦ by
        simp [evalPolynomial, Variety.prodPointEquiv]⟩ }
  map_one := rfl
  map_mul := by intro x y; rfl

/-- Canonical injection into the first direct-product factor. -/
@[expose]
public def Morphism.inl (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Theory.AlgebraicGroup.Morphism G (Variety.prod G H) where
  toVariety :=
    { toFun := fun x ↦ (Variety.prodPointEquiv G H).symm (x, 1)
      regular := by
        intro i
        cases i with
        | inl i =>
            exact ⟨MvPolynomial.X i, fun x ↦ by
              simp [evalPolynomial, Variety.prodPointEquiv]⟩
        | inr i =>
            exact ⟨MvPolynomial.C ((1 : Variety.Point H).val i), fun x ↦ by
              simp [evalPolynomial, Variety.prodPointEquiv]⟩ }
  map_one := by
    apply (Variety.prodPointEquiv G H).injective
    rfl
  map_mul := by
    intro x y
    apply (Variety.prodPointEquiv G H).injective
    rw [Equiv.apply_symm_apply, Variety.prodPointEquiv_mul,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp

/-- Canonical injection into the second direct-product factor. -/
@[expose]
public def Morphism.inr (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Theory.AlgebraicGroup.Morphism H (Variety.prod G H) where
  toVariety :=
    { toFun := fun y ↦ (Variety.prodPointEquiv G H).symm (1, y)
      regular := by
        intro i
        cases i with
        | inl i =>
            exact ⟨MvPolynomial.C ((1 : Variety.Point G).val i), fun y ↦ by
              simp [evalPolynomial, Variety.prodPointEquiv]⟩
        | inr i =>
            exact ⟨MvPolynomial.X i, fun y ↦ by
              simp [evalPolynomial, Variety.prodPointEquiv]⟩ }
  map_one := by
    apply (Variety.prodPointEquiv G H).injective
    rfl
  map_mul := by
    intro x y
    apply (Variety.prodPointEquiv G H).injective
    rw [Equiv.apply_symm_apply, Variety.prodPointEquiv_mul,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp

/-- Pairing of two algebraic-group morphisms into a direct product. -/
@[expose]
public def Morphism.prod {X G H : Variety k}
    [AlgebraicGroup X] [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism X G) (g : Theory.AlgebraicGroup.Morphism X H) :
    Theory.AlgebraicGroup.Morphism X (Variety.prod G H) where
  toVariety :=
    { toFun := fun x ↦ (Variety.prodPointEquiv G H).symm
          (f.toVariety.toFun x, g.toVariety.toFun x)
      regular := by
        intro i
        cases i with
        | inl i =>
            rcases f.toVariety.regular i with ⟨p, hp⟩
            exact ⟨p, fun x ↦ by
              simpa [Variety.prodPointEquiv] using hp x⟩
        | inr i =>
            rcases g.toVariety.regular i with ⟨p, hp⟩
            exact ⟨p, fun x ↦ by
              simpa [Variety.prodPointEquiv] using hp x⟩ }
  map_one := by
    apply (Variety.prodPointEquiv G H).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext f.map_one g.map_one
  map_mul := by
    intro x y
    apply (Variety.prodPointEquiv G H).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (f.map_mul x y) (g.map_mul x y)

/-- The first product projection retracts the left product inclusion. -/
public lemma product_fst_inl (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    ∀ x, (Theory.AlgebraicGroup.Morphism.fst G H).onPoints
      ((Theory.AlgebraicGroup.Morphism.inl G H).onPoints x) = x := by
  intro x
  simp [Theory.AlgebraicGroup.Morphism.fst, Theory.AlgebraicGroup.Morphism.inl,
    Theory.AlgebraicGroup.Morphism.onPoints]

/-- The second product projection retracts the right product inclusion. -/
public lemma product_snd_inr (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    ∀ y, (Theory.AlgebraicGroup.Morphism.snd G H).onPoints
      ((Theory.AlgebraicGroup.Morphism.inr G H).onPoints y) = y := by
  intro y
  simp [Theory.AlgebraicGroup.Morphism.snd, Theory.AlgebraicGroup.Morphism.inr,
    Theory.AlgebraicGroup.Morphism.onPoints]

/-- The left product inclusion is injective on points. -/
public lemma product_inl_injective (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Function.Injective (Theory.AlgebraicGroup.Morphism.inl G H).onPoints :=
  Function.LeftInverse.injective (product_fst_inl G H)

/-- The right product inclusion is injective on points. -/
public lemma product_inr_injective (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] :
    Function.Injective (Theory.AlgebraicGroup.Morphism.inr G H).onPoints :=
  Function.LeftInverse.injective (product_snd_inr G H)

/-- Proposition 1.1.2(d): a pair of algebraic-group morphisms has a unique
morphism to the direct product with the prescribed projections. -/
public theorem productMorphism_existsUnique
    (G H X : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] [AlgebraicGroup X]
    (f : Theory.AlgebraicGroup.Morphism X G) (g : Theory.AlgebraicGroup.Morphism X H) :
    ∃! h : Theory.AlgebraicGroup.Morphism X (Variety.prod G H),
      (∀ x, (Theory.AlgebraicGroup.Morphism.fst G H).onPoints (h.onPoints x) =
        f.onPoints x) ∧
      (∀ x, (Theory.AlgebraicGroup.Morphism.snd G H).onPoints (h.onPoints x) =
        g.onPoints x) := by
  let h := Theory.AlgebraicGroup.Morphism.prod f g
  refine ⟨h, ?_, ?_⟩
  · constructor <;> intro x <;>
      simp [h, Theory.AlgebraicGroup.Morphism.prod, Theory.AlgebraicGroup.Morphism.fst,
        Theory.AlgebraicGroup.Morphism.snd, Theory.AlgebraicGroup.Morphism.onPoints]
  · intro q hq
    apply Theory.AlgebraicGroup.Morphism.ext
    funext x
    apply (Variety.prodPointEquiv G H).injective
    apply Prod.ext
    · exact hq.1 x
    · exact hq.2 x

end Theory.AlgebraicGroup

