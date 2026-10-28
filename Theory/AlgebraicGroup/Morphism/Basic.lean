module

public import Theory.AlgebraicGroup.Basic
public import Theory.AlgebraicGroup.Variety.Morphism

universe u

/-! Algebraic-group morphisms and their underlying point homomorphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- An algebraic-group morphism is a polynomial morphism preserving the group
operation and identity. -/
public structure Morphism (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] where
  toVariety : Variety.Morphism G H
  map_one : toVariety.toFun 1 = 1
  map_mul : ∀ x y, toVariety.toFun (x * y) = toVariety.toFun x * toVariety.toFun y

/-- The induced map on rational points. -/
@[expose]
public def Morphism.onPoints {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (f : Theory.AlgebraicGroup.Morphism G H) :
    Variety.Point G →* Variety.Point H where
  toFun := f.toVariety.toFun
  map_one' := f.map_one
  map_mul' := f.map_mul

/-- Identity algebraic-group morphism. -/
@[expose]
public def Morphism.id (G : Variety k) [AlgebraicGroup G] :
    Theory.AlgebraicGroup.Morphism G G where
  toVariety := Variety.Morphism.id G
  map_one := rfl
  map_mul := by intro x y; rfl

/-- Composition of algebraic-group morphisms. -/
@[expose]
public def Morphism.comp {G H I : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] [AlgebraicGroup I]
    (g : Theory.AlgebraicGroup.Morphism H I) (f : Theory.AlgebraicGroup.Morphism G H) :
    Theory.AlgebraicGroup.Morphism G I where
  toVariety := g.toVariety.comp f.toVariety
  map_one := by
    simp only [Variety.Morphism.comp]
    rw [f.map_one, g.map_one]
  map_mul := by
    intro x y
    simp only [Variety.Morphism.comp]
    rw [f.map_mul, g.map_mul]

/-- Algebraic-group morphisms are determined by their point maps. -/
public lemma Morphism.ext {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (f g : Theory.AlgebraicGroup.Morphism G H)
    (h : f.toVariety.toFun = g.toVariety.toFun) : f = g := by
  cases f with
  | mk f hfOne hfMul =>
      cases g with
      | mk g hgOne hgMul =>
          have hfg : f = g := Variety.Morphism.ext f g h
          cases hfg
          rfl

public lemma Morphism.comp_id
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    f.comp (Theory.AlgebraicGroup.Morphism.id G) = f := by
  apply Theory.AlgebraicGroup.Morphism.ext
  rfl

public lemma Morphism.id_comp
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H) :
    (Theory.AlgebraicGroup.Morphism.id H).comp f = f := by
  apply Theory.AlgebraicGroup.Morphism.ext
  rfl

public lemma Morphism.comp_assoc
    {G H I J : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] [AlgebraicGroup I]
    [AlgebraicGroup J]
    (h : Theory.AlgebraicGroup.Morphism I J)
    (g : Theory.AlgebraicGroup.Morphism H I)
    (f : Theory.AlgebraicGroup.Morphism G H) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  apply Theory.AlgebraicGroup.Morphism.ext
  rfl

/-- Algebraic-group morphisms preserve inverses. -/
public lemma Morphism.map_inv {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (f : Theory.AlgebraicGroup.Morphism G H)
    (x : Variety.Point G) : f.onPoints x⁻¹ = (f.onPoints x)⁻¹ :=
  f.onPoints.map_inv x

/-- Algebraic-group morphisms preserve integral powers. -/
public lemma Morphism.map_zpow {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (f : Theory.AlgebraicGroup.Morphism G H)
    (x : Variety.Point G) (n : ℤ) : f.onPoints (x ^ n) = f.onPoints x ^ n :=
  f.onPoints.map_zpow x n

/-- The kernel subgroup of an algebraic-group morphism. -/
@[expose]
public def Morphism.kernel {G H : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] (f : Theory.AlgebraicGroup.Morphism G H) :
    Subgroup (Variety.Point G) := f.onPoints.ker

end Theory.AlgebraicGroup
