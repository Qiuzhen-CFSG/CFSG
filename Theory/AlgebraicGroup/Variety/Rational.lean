module

public import Theory.AlgebraicGroup.Variety.PolynomialFunction

universe u

/-! Rational self-maps of affine varieties in the sense of GLS §1.2. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A self-map is rational when it pulls polynomial functions back to
polynomial functions. -/
@[expose]
public def IsRationalMap (G : Variety k)
    (ψ : Variety.Point G → Variety.Point G) : Prop :=
  ∀ f : Variety.PolynomialFunction G,
    (fun x : Variety.Point G => f (ψ x)) ∈
      (Variety.polynomialFunctionSubring G : Set (Variety.Point G → k))

/-- The underlying map of a polynomial morphism is rational. -/
public lemma Variety.Morphism.toFun_isRational
    {G : Variety k} (f : Variety.Morphism G G) :
    IsRationalMap G f.toFun := by
  intro a
  simpa [Variety.PolynomialFunction.pullback] using
    (Variety.PolynomialFunction.pullback f a).2

/-- Every rational self-map is represented by a polynomial morphism. -/
public theorem IsRationalMap.exists_morphism {G : Variety k}
    (ψ : Variety.Point G → Variety.Point G) (hψ : IsRationalMap G ψ) :
    ∃ f : Variety.Morphism G G, f.toFun = ψ := by
  have hreg : ∀ i : G.Coordinates, ∃ p : MvPolynomial G.Coordinates k,
      ∀ x : Variety.Point G, (ψ x).val i = evalPolynomial x.val p := by
    intro i
    obtain ⟨p, hp⟩ := hψ
      (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i))
    refine ⟨p, ?_⟩
    intro x
    have hv :
        (Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)) (ψ x) =
          (ψ x).val i := by
      simp [Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun, evalPolynomial]
    rw [← hv]
    exact hp x
  choose p hp using hreg
  exact ⟨⟨ψ, fun i => ⟨p i, hp i⟩⟩, rfl⟩

end Theory.AlgebraicGroup
