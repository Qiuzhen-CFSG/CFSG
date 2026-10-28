module

public import Theory.AlgebraicGroup.Variety.Morphism

universe u

/-!
Polynomial functions on presented affine varieties and pullback along morphisms.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- Polynomial functions on an affine zero locus form the subring of all
pointwise functions represented by ambient polynomials.  Equality is equality
of functions on the zero locus, so different defining equations or polynomial
representatives do not create distinct functions.  The carrier is the ring of
functions on the `k`-rational points only: over an algebraically closed field
this is the reduced affine coordinate ring, but in general it is not the
coordinate ring of the presented scheme. -/
@[expose]
public def Variety.polynomialFunctionSubring (V : Variety k) :
    Subring (Variety.Point V → k) where
  carrier := {f | ∃ p : MvPolynomial V.Coordinates k,
    ∀ x : Variety.Point V, f x = evalPolynomial x.val p}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro x
    simp [evalPolynomial]
  one_mem' := by
    refine ⟨1, ?_⟩
    intro x
    simp [evalPolynomial]
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨p, hp⟩
    rcases hg with ⟨q, hq⟩
    refine ⟨p + q, ?_⟩
    intro x
    simp [hp, hq, evalPolynomial]
  mul_mem' := by
    intro f g hf hg
    rcases hf with ⟨p, hp⟩
    rcases hg with ⟨q, hq⟩
    refine ⟨p * q, ?_⟩
    intro x
    simp [hp, hq, evalPolynomial]
  neg_mem' := by
    intro f hf
    rcases hf with ⟨p, hp⟩
    refine ⟨-p, ?_⟩
    intro x
    simp [hp, evalPolynomial]

/-- The actual affine algebra of polynomial functions on a zero locus. -/
public abbrev Variety.PolynomialFunction (V : Variety k) : Type u :=
  V.polynomialFunctionSubring

@[expose]
public def Variety.PolynomialFunction.toFun {V : Variety k}
    (a : Variety.PolynomialFunction V) : Variety.Point V → k :=
  a.1

public instance Variety.PolynomialFunction.coeFun (V : Variety k) :
    CoeFun (Variety.PolynomialFunction V) (fun _ ↦ Variety.Point V → k) :=
  ⟨Variety.PolynomialFunction.toFun⟩

public lemma Variety.PolynomialFunction.ext {V : Variety k}
    {a b : Variety.PolynomialFunction V}
    (h : ∀ x, a x = b x) : a = b := by
  apply Subtype.ext
  funext x
  exact h x

public lemma Variety.PolynomialFunction.representedBy {V : Variety k}
    (a : Variety.PolynomialFunction V) :
    ∃ p : MvPolynomial V.Coordinates k,
      ∀ x : Variety.Point V, a x = evalPolynomial x.val p :=
  a.2

/-- The polynomial function represented by a specified polynomial. -/
@[expose]
public def Variety.PolynomialFunction.ofPolynomial (V : Variety k)
    (p : MvPolynomial V.Coordinates k) :
    Variety.PolynomialFunction V :=
  ⟨fun x ↦ evalPolynomial x.val p, ⟨p, fun _ ↦ rfl⟩⟩

/-- Pullback of polynomial functions along a polynomial morphism. -/
@[expose]
public def Variety.PolynomialFunction.pullback {V W : Variety k}
    (f : Variety.Morphism V W) (a : Variety.PolynomialFunction W) :
    Variety.PolynomialFunction V := by
  refine ⟨fun x ↦ a (f.toFun x), ?_⟩
  ·
    rcases a.representedBy with ⟨p, hp⟩
    let coordinatePolynomial : W.Coordinates →
        MvPolynomial V.Coordinates k :=
      fun i ↦ Classical.choose (f.regular i)
    refine ⟨MvPolynomial.bind₁ coordinatePolynomial p, ?_⟩
    intro x
    rw [evalPolynomial_bind₁]
    change a (f.toFun x) = _
    rw [hp]
    congr 1
    funext i
    exact Classical.choose_spec (f.regular i) x

/-- Pullback of polynomial functions is an actual ring homomorphism. -/
@[expose]
public def Variety.Morphism.pullbackRingHom {V W : Variety k}
    (f : Variety.Morphism V W) :
      Variety.PolynomialFunction W →+* Variety.PolynomialFunction V where
  toFun := Variety.PolynomialFunction.pullback f
  map_one' := by
    apply Variety.PolynomialFunction.ext
    intro x
    rfl
  map_mul' := by
    intro a b
    apply Variety.PolynomialFunction.ext
    intro x
    rfl
  map_zero' := by
    apply Variety.PolynomialFunction.ext
    intro x
    rfl
  map_add' := by
    intro a b
    apply Variety.PolynomialFunction.ext
    intro x
    rfl

public lemma Variety.Morphism.pullbackRingHom_apply
    {V W : Variety k} (f : Variety.Morphism V W)
    (a : Variety.PolynomialFunction W) :
    f.pullbackRingHom a = Variety.PolynomialFunction.pullback f a := rfl

public lemma Variety.Morphism.pullbackRingHom_id
    (V : Variety k) :
    (Variety.Morphism.id V).pullbackRingHom =
      RingHom.id (Variety.PolynomialFunction V) := by
  apply RingHom.ext
  intro a
  apply Variety.PolynomialFunction.ext
  intro x
  rfl

public lemma Variety.Morphism.pullbackRingHom_comp
    {U V W : Variety k} (g : Variety.Morphism V W)
    (f : Variety.Morphism U V) :
    (g.comp f).pullbackRingHom =
      f.pullbackRingHom.comp g.pullbackRingHom := by
  apply RingHom.ext
  intro a
  apply Variety.PolynomialFunction.ext
  intro x
  rfl

end Theory.AlgebraicGroup
