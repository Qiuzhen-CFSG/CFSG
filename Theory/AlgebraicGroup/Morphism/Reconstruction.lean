module

public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction
public import Theory.AlgebraicGroup.Morphism.Basic

universe u

/-! Reconstructing algebraic-group morphisms from point homomorphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A point-group homomorphism represented by a polynomial-function algebra
homomorphism is regular. -/
public lemma Morphism.exists_of_pointHom_of_polynomialFunctionAlgHom
    {Q I : Variety k} [AlgebraicGroup Q] [AlgebraicGroup I]
    (ψ : Variety.Point Q →* Variety.Point I)
    (α : Variety.PolynomialFunction I →ₐ[k] Variety.PolynomialFunction Q)
    (hα : ∀ a y, α a y = a (ψ y)) :
    ∃ f : AlgebraicGroup.Morphism Q I, f.onPoints = ψ := by
  let f : AlgebraicGroup.Morphism Q I :=
    { toVariety :=
        { toFun := ψ
          regular := by
            intro j
            let coordinate : Variety.PolynomialFunction I :=
              Variety.PolynomialFunction.ofPolynomial I (MvPolynomial.X j)
            rcases (α coordinate).representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro y
            rw [← hp y]
            simpa [coordinate, Variety.PolynomialFunction.ofPolynomial,
              Variety.PolynomialFunction.toFun, evalPolynomial] using
              (hα coordinate y).symm }
      map_one := ψ.map_one
      map_mul := ψ.map_mul }
  exact ⟨f, rfl⟩

/-- A point-group lift through a point-surjective morphism is regular when the
pullback on polynomial functions is surjective. -/
public lemma Morphism.exists_of_pointHom_of_pullback_surjective
    {G Q I : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup Q] [AlgebraicGroup I]
    (π : AlgebraicGroup.Morphism G Q)
    (hπ : Function.Surjective π.onPoints)
    (hpull : Function.Surjective π.toVariety.pullbackRingHom)
    (φ : AlgebraicGroup.Morphism G I)
    (ψ : Variety.Point Q →* Variety.Point I)
    (hψ : ψ.comp π.onPoints = φ.onPoints) :
    ∃ f : AlgebraicGroup.Morphism Q I, f.onPoints = ψ := by
  let f : AlgebraicGroup.Morphism Q I :=
    { toVariety :=
        { toFun := ψ
          regular := by
            intro j
            let coordinate : Variety.PolynomialFunction I :=
              Variety.PolynomialFunction.ofPolynomial I (MvPolynomial.X j)
            obtain ⟨q, hq⟩ := hpull
              (Variety.PolynomialFunction.pullback φ.toVariety coordinate)
            rcases q.representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro y
            rcases hπ y with ⟨x, rfl⟩
            have hpoint := congrArg
              (fun m : Variety.Point G →* Variety.Point I ↦ m x) hψ
            have hcoord := congrArg (fun y : Variety.Point I ↦ y.val j) hpoint
            change (ψ (π.onPoints x)).val j = (φ.onPoints x).val j at hcoord
            have hfun := congrArg
              (fun r : Variety.PolynomialFunction G ↦ r x) hq
            change (ψ (π.onPoints x)).val j =
              evalPolynomial (π.onPoints x).val p
            rw [hcoord, ← hp (π.onPoints x)]
            have hfun' : (φ.toVariety.toFun x).val j =
                q (π.toVariety.toFun x) := by
              simpa [Variety.Morphism.pullbackRingHom_apply,
                Variety.PolynomialFunction.pullback, coordinate,
                Variety.PolynomialFunction.ofPolynomial,
                Variety.PolynomialFunction.toFun, evalPolynomial] using hfun.symm
            simpa [AlgebraicGroup.Morphism.onPoints] using hfun' }
      map_one := ψ.map_one
      map_mul := ψ.map_mul }
  exact ⟨f, rfl⟩

end Theory.AlgebraicGroup
