module

public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction

universe u

/-! Iteration of affine-variety endomorphisms and its pullback action. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The `n`-fold iterate of an endomorphism morphism. -/
public def Variety.Morphism.iterate {V : Variety k}
    (f : Variety.Morphism V V) : ℕ → Variety.Morphism V V
  | 0 => Variety.Morphism.id V
  | n + 1 => (f.iterate n).comp f

/-- The underlying map of a morphism iterate is the corresponding function
iterate. -/
public lemma Variety.Morphism.iterate_toFun {V : Variety k}
    (f : Variety.Morphism V V) (n : ℕ) :
    (f.iterate n).toFun = f.toFun^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      change (f.iterate n).toFun (f.toFun x) = f.toFun^[n + 1] x
      rw [ih]
      rfl

/-- Pullback on rings sends a morphism iterate to the corresponding function
iterate. -/
public lemma Variety.Morphism.pullbackRingHom_iterate {V : Variety k}
    (f : Variety.Morphism V V) (n : ℕ) :
    (f.iterate n).pullbackRingHom = f.pullbackRingHom^[n] := by
  induction n with
  | zero =>
      rw [Variety.Morphism.iterate, Variety.Morphism.pullbackRingHom_id]
      rfl
  | succ n ih =>
      rw [Variety.Morphism.iterate, Variety.Morphism.pullbackRingHom_comp]
      funext a
      apply Variety.PolynomialFunction.ext
      intro x
      change f.pullbackRingHom ((f.iterate n).pullbackRingHom a) x =
        (f.pullbackRingHom^[n + 1]) a x
      rw [ih, Function.iterate_succ']
      rfl

/-- Pullback reverses composition of polynomial morphisms. -/
public lemma Variety.Morphism.pullbackAlgHom_comp {U V W : Variety k}
    (g : Variety.Morphism V W) (f : Variety.Morphism U V) :
    (g.comp f).pullbackAlgHom = f.pullbackAlgHom.comp g.pullbackAlgHom := by
  apply AlgHom.ext
  intro a
  apply Variety.PolynomialFunction.ext
  intro x
  rfl

/-- The iterate of the pullback linear map is the pullback of the morphism
iterate. -/
public lemma Variety.Morphism.pullbackAlgHom_iterate {V : Variety k}
    (f : Variety.Morphism V V) (n : ℕ) :
    f.pullbackAlgHom.toLinearMap^[n] =
      (f.iterate n).pullbackAlgHom.toLinearMap := by
  induction n with
  | zero =>
      simp [Variety.Morphism.iterate]
      ext a
      rfl
  | succ n ih =>
      rw [Function.iterate_succ', Variety.Morphism.iterate,
        Variety.Morphism.pullbackAlgHom_comp, ih]
      rfl

end Theory.AlgebraicGroup
