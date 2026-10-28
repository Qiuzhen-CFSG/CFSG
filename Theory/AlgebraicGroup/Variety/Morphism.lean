module

public import Theory.AlgebraicGroup.Variety.Defs

universe u

/-!
Polynomial morphisms of presented affine varieties and affine products.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- A polynomial morphism between affine zero loci. -/
public structure Variety.Morphism (V W : Variety k) where
  toFun : Variety.Point V → Variety.Point W
  regular : ∀ i : W.Coordinates, ∃ p : MvPolynomial V.Coordinates k,
    ∀ x : Variety.Point V, (toFun x).val i = evalPolynomial x.val p

/-- Identity polynomial morphism. -/
@[expose]
public def Variety.Morphism.id (V : Variety k) : Variety.Morphism V V where
  toFun := fun x ↦ x
  regular := fun i ↦ ⟨MvPolynomial.X i, fun x ↦ by simp [evalPolynomial]⟩

/-- Composition of polynomial morphisms. -/
@[expose]
public def Variety.Morphism.comp {U V W : Variety k}
    (g : Variety.Morphism V W) (f : Variety.Morphism U V) :
    Variety.Morphism U W where
  toFun := fun x ↦ g.toFun (f.toFun x)
  regular := by
    intro i
    rcases g.regular i with ⟨p, hp⟩
    let coordinatePolynomial : V.Coordinates →
        MvPolynomial U.Coordinates k :=
      fun j ↦ Classical.choose (f.regular j)
    refine ⟨MvPolynomial.bind₁ coordinatePolynomial p, ?_⟩
    intro x
    rw [evalPolynomial_bind₁]
    rw [hp]
    congr 1
    funext j
    exact Classical.choose_spec (f.regular j) x

/-- A constant polynomial morphism. -/
@[expose]
public def Variety.Morphism.const (V W : Variety k) (y : Variety.Point W) :
    Variety.Morphism V W where
  toFun := fun _ ↦ y
  regular := fun i ↦ ⟨MvPolynomial.C (y.val i), fun x ↦ by
    simp [evalPolynomial]⟩

/-- Polynomial morphisms are determined by their point maps. -/
public lemma Variety.Morphism.ext {V W : Variety k}
    (f g : Variety.Morphism V W) (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

public lemma Variety.Morphism.comp_id {V W : Variety k}
    (f : Variety.Morphism V W) :
    f.comp (Variety.Morphism.id V) = f := by
  apply Variety.Morphism.ext
  rfl

public lemma Variety.Morphism.id_comp {V W : Variety k}
    (f : Variety.Morphism V W) :
    (Variety.Morphism.id W).comp f = f := by
  apply Variety.Morphism.ext
  rfl

public lemma Variety.Morphism.comp_assoc
    {U V W X : Variety k}
    (h : Variety.Morphism W X) (g : Variety.Morphism V W)
    (f : Variety.Morphism U V) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  apply Variety.Morphism.ext
  rfl

/-- The affine product zero locus. -/
public abbrev Variety.prod (V W : Variety k) : Variety k where
  Coordinates := V.Coordinates ⊕ W.Coordinates
  finiteCoordinates := inferInstance
  equations :=
    MvPolynomial.rename Sum.inl '' V.equations ∪
      MvPolynomial.rename Sum.inr '' W.equations

/-- Points of the affine product are pairs of points. -/
@[expose]
public def Variety.prodPointEquiv (V W : Variety k) :
    Variety.Point (Variety.prod V W) ≃ Variety.Point V × Variety.Point W where
  toFun := fun x ↦
    (⟨fun i ↦ x.val (Sum.inl i), by
        intro p hp
        have hx := x.isZero (MvPolynomial.rename Sum.inl p)
          (Set.mem_union_left _ ⟨p, hp, rfl⟩)
        rw [evalPolynomial_rename] at hx
        exact hx⟩,
      ⟨fun i ↦ x.val (Sum.inr i), by
        intro p hp
        have hx := x.isZero (MvPolynomial.rename Sum.inr p)
          (Set.mem_union_right _ ⟨p, hp, rfl⟩)
        rw [evalPolynomial_rename] at hx
        exact hx⟩)
  invFun := fun x ↦
    ⟨Sum.elim x.1.val x.2.val, by
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · rw [evalPolynomial_rename]
        exact x.1.isZero q hq
      · rw [evalPolynomial_rename]
        exact x.2.isZero q hq⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext i
    cases i <;> rfl
  right_inv := by
    intro x
    apply Prod.ext
    · apply Variety.Point.ext
      rfl
    · apply Variety.Point.ext
      rfl

/-- First projection of affine varieties. -/
@[expose]
public def Variety.Morphism.fst (V W : Variety k) :
    Variety.Morphism (Variety.prod V W) V where
  toFun := fun z ↦ (Variety.prodPointEquiv V W z).1
  regular := fun i ↦ ⟨MvPolynomial.X (Sum.inl i), fun z ↦ by
    simp [evalPolynomial, Variety.prodPointEquiv]⟩

/-- Second projection of affine varieties. -/
@[expose]
public def Variety.Morphism.snd (V W : Variety k) :
    Variety.Morphism (Variety.prod V W) W where
  toFun := fun z ↦ (Variety.prodPointEquiv V W z).2
  regular := fun i ↦ ⟨MvPolynomial.X (Sum.inr i), fun z ↦ by
    simp [evalPolynomial, Variety.prodPointEquiv]⟩

/-- Pairing of polynomial morphisms into an affine product. -/
@[expose]
public def Variety.Morphism.pair {U V W : Variety k}
    (f : Variety.Morphism U V) (g : Variety.Morphism U W) :
    Variety.Morphism U (Variety.prod V W) where
  toFun := fun x ↦ (Variety.prodPointEquiv V W).symm (f.toFun x, g.toFun x)
  regular := by
    intro i
    cases i with
    | inl i =>
        rcases f.regular i with ⟨p, hp⟩
        exact ⟨p, fun x ↦ by
          simpa [Variety.prodPointEquiv] using hp x⟩
    | inr i =>
        rcases g.regular i with ⟨p, hp⟩
        exact ⟨p, fun x ↦ by
          simpa [Variety.prodPointEquiv] using hp x⟩

end Theory.AlgebraicGroup
