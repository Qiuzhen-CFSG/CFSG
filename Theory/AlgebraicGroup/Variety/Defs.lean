module

public import Mathlib.Algebra.MvPolynomial.Monad

universe u

/-!
Presented affine varieties, rational points, polynomial evaluation, and elementary closed-subvariety constructions.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- Evaluation of a polynomial at an affine point. -/
@[expose]
public def evalPolynomial {σ : Type*} (x : σ → k)
    (p : MvPolynomial σ k) : k :=
  MvPolynomial.eval₂ (RingHom.id k) x p

public lemma evalPolynomial_bind₁ {σ τ : Type*} (x : τ → k)
    (f : σ → MvPolynomial τ k) (p : MvPolynomial σ k) :
    evalPolynomial x (MvPolynomial.bind₁ f p) =
      evalPolynomial (fun i ↦ evalPolynomial x (f i)) p := by
  simpa [evalPolynomial] using
    (MvPolynomial.eval₂Hom_bind₁ (RingHom.id k) x f p)

public lemma evalPolynomial_rename {σ τ : Type*} (x : τ → k)
    (f : σ → τ) (p : MvPolynomial σ k) :
    evalPolynomial x (MvPolynomial.rename f p) =
      evalPolynomial (x ∘ f) p := by
  simpa [evalPolynomial] using
    (MvPolynomial.eval₂_rename (RingHom.id k) f x p)

public lemma evalPolynomial_sum {σ ι : Type*} [Fintype ι]
    (x : σ → k) (p : ι → MvPolynomial σ k) :
    evalPolynomial x (∑ i, p i) = ∑ i, evalPolynomial x (p i) := by
  simp [evalPolynomial]

public lemma evalPolynomial_mul {σ : Type*} (x : σ → k)
    (p q : MvPolynomial σ k) :
    evalPolynomial x (p * q) = evalPolynomial x p * evalPolynomial x q := by
  simp [evalPolynomial]

public lemma evalPolynomial_X {σ : Type*} (x : σ → k) (i : σ) :
    evalPolynomial x (MvPolynomial.X i) = x i := by
  simp [evalPolynomial]

/-- An affine variety presented as the common zero locus of polynomial
equations. -/
public structure Variety (k : Type u) [Field k] where
  Coordinates : Type u
  finiteCoordinates : Finite Coordinates
  equations : Set (MvPolynomial Coordinates k)

public noncomputable instance Variety.instFintypeCoordinates (V : Variety k) :
    Fintype V.Coordinates := by
  letI := V.finiteCoordinates
  exact Fintype.ofFinite V.Coordinates

/-- The set of `k`-rational points of a presented variety. -/
public structure Variety.Point (V : Variety k) where
  val : V.Coordinates → k
  isZero : ∀ p ∈ V.equations, evalPolynomial val p = 0

/-- Two rational points are equal when all their coordinates are equal. -/
public lemma Variety.Point.ext {V : Variety k} {x y : Variety.Point V}
    (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

end Theory.AlgebraicGroup

