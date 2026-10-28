module

public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction

universe u

/-! Reconstructing affine points and morphisms from polynomial-function
algebra homomorphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Evaluation of polynomial functions at a point as an algebra homomorphism. -/
@[expose]
public noncomputable def Variety.PolynomialFunction.evalAlgHom (V : Variety k)
    (x : Variety.Point V) :
    Variety.PolynomialFunction V →ₐ[k] k where
  toFun := fun f ↦ f x
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
  commutes' := fun r ↦ polynomialFunction_algebraMap_apply V r x

/-- Coordinate values determined by an algebra homomorphism to the field. -/
@[expose]
public noncomputable def Variety.algHomCoordinates (V : Variety k)
    (φ : Variety.PolynomialFunction V →ₐ[k] k) : V.Coordinates → k :=
  fun i ↦ φ (Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.X i))

/-- Applying an algebra homomorphism to a represented polynomial function is
evaluation at its reconstructed coordinate tuple. -/
public lemma Variety.algHom_ofPolynomial_eq_eval (V : Variety k)
    (φ : Variety.PolynomialFunction V →ₐ[k] k)
    (p : MvPolynomial V.Coordinates k) :
    φ (Variety.PolynomialFunction.ofPolynomial V p) =
      evalPolynomial (Variety.algHomCoordinates V φ) p := by
  let lhs : MvPolynomial V.Coordinates k →ₐ[k] k :=
    φ.comp (evaluationAlgHom V)
  let rhs : MvPolynomial V.Coordinates k →ₐ[k] k :=
    MvPolynomial.eval₂AlgHom k (Variety.algHomCoordinates V φ)
  have h : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [lhs, rhs, evaluationAlgHom, evaluationRingHom,
      Variety.algHomCoordinates]
  exact DFunLike.congr_fun h p

/-- The point reconstructed from an algebra homomorphism to the ground field. -/
@[expose]
public noncomputable def Variety.pointOfPolynomialFunctionAlgHom (V : Variety k)
    (φ : Variety.PolynomialFunction V →ₐ[k] k) : Variety.Point V where
  val := Variety.algHomCoordinates V φ
  isZero := by
    intro p hp
    have heval := Variety.algHom_ofPolynomial_eq_eval V φ p
    have hzero : Variety.PolynomialFunction.ofPolynomial V p = 0 := by
      apply Variety.PolynomialFunction.ext
      intro x
      change evalPolynomial x.val p = 0
      exact x.isZero p hp
    rw [hzero, map_zero] at heval
    exact heval.symm

/-- Every polynomial function evaluates at the reconstructed point to its
image under the algebra homomorphism. -/
public lemma Variety.pointOfPolynomialFunctionAlgHom_apply (V : Variety k)
    (φ : Variety.PolynomialFunction V →ₐ[k] k)
    (f : Variety.PolynomialFunction V) :
    f (Variety.pointOfPolynomialFunctionAlgHom V φ) = φ f := by
  rcases f.representedBy with ⟨p, hp⟩
  have hf : f = Variety.PolynomialFunction.ofPolynomial V p := by
    apply Variety.PolynomialFunction.ext
    intro x
    exact hp x
  rw [hf]
  exact (Variety.algHom_ofPolynomial_eq_eval V φ p).symm

/-- The polynomial morphism contravariantly determined by a homomorphism of
polynomial-function algebras. -/
@[expose]
public noncomputable def Variety.Morphism.ofPolynomialFunctionAlgHom {V W : Variety k}
    (F : Variety.PolynomialFunction W →ₐ[k]
      Variety.PolynomialFunction V) : Variety.Morphism V W where
  toFun := fun x ↦ Variety.pointOfPolynomialFunctionAlgHom W
    ((Variety.PolynomialFunction.evalAlgHom V x).comp F)
  regular := by
    intro i
    rcases (F (Variety.PolynomialFunction.ofPolynomial W
      (MvPolynomial.X i))).representedBy with ⟨p, hp⟩
    exact ⟨p, hp⟩

/-- Reconstructing a polynomial morphism from an algebra homomorphism recovers
that homomorphism as pullback. -/
public lemma Variety.Morphism.pullbackAlgHom_ofPolynomialFunctionAlgHom
    {V W : Variety k}
    (F : Variety.PolynomialFunction W →ₐ[k]
      Variety.PolynomialFunction V) :
    (Variety.Morphism.ofPolynomialFunctionAlgHom F).pullbackAlgHom = F := by
  apply AlgHom.ext
  intro f
  apply Variety.PolynomialFunction.ext
  intro x
  change f (Variety.pointOfPolynomialFunctionAlgHom W
    ((Variety.PolynomialFunction.evalAlgHom V x).comp F)) = F f x
  rw [Variety.pointOfPolynomialFunctionAlgHom_apply]
  rfl

end Theory.AlgebraicGroup
