module

public import Theory.AlgebraicGroup.CoordinateRing.Point

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A morphism of affine varieties is injective on points when every regular
function on its source is pulled back from its target. -/
public theorem Variety.Morphism.injective_of_pullbackRingHom_surjective
    {V W : Variety k} (f : Variety.Morphism V W)
    (hpull : Function.Surjective f.pullbackRingHom) :
    Function.Injective f.toFun := by
  intro x y hxy
  apply Variety.Point.ext
  funext c
  let q : Variety.PolynomialFunction V :=
    Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.X c)
  obtain ⟨p, hp⟩ := hpull q
  have hpx := congrArg (fun a : Variety.PolynomialFunction V => a x) hp
  have hpy := congrArg (fun a : Variety.PolynomialFunction V => a y) hp
  change p (f.toFun x) = q x at hpx
  change p (f.toFun y) = q y at hpy
  calc
    x.val c = q x := by
      dsimp [q, Variety.PolynomialFunction.toFun,
        Variety.PolynomialFunction.ofPolynomial]
      rw [evalPolynomial_X]
    _ = p (f.toFun x) := hpx.symm
    _ = p (f.toFun y) := congrArg p hxy
    _ = q y := hpy
    _ = y.val c := by
      dsimp [q, Variety.PolynomialFunction.toFun,
        Variety.PolynomialFunction.ofPolynomial]
      rw [evalPolynomial_X]

end Theory.AlgebraicGroup
