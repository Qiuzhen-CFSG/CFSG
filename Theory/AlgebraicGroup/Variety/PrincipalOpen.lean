module

public import Theory.AlgebraicGroup.Variety.PolynomialFunction
public import Theory.AlgebraicGroup.Variety.Zariski

universe u

/-!
Principal opens in a presented affine variety.  For a finite family of ambient
polynomials we record the locus on which every member is nonzero, prove
directly from the zero-locus definition that this locus is Zariski open, and
package the polynomial and quotient functions needed for inverse determinant
and cofactor formulas.  The construction is the rational-point version of
the principal-open presentation `V_f = {(x, λ) | λ f(x) = 1}` from GLS,
Chapter 2, §2.2.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

variable {k : Type u} [Field k]

/-- The principal-open locus on which every member of a finite polynomial
family is nonzero. -/
@[expose]
public def Variety.principalOpenLocus {ι : Type*} [Fintype ι]
    (V : Variety k) (f : ι → MvPolynomial V.Coordinates k) :
    Set (Variety.Point V) :=
  {x | ∀ i, evalPolynomial x.val (f i) ≠ 0}

@[simp] public theorem Variety.mem_principalOpenLocus
    {ι : Type*} [Fintype ι] (V : Variety k)
    (f : ι → MvPolynomial V.Coordinates k) (x : Variety.Point V) :
    x ∈ V.principalOpenLocus f ↔
      ∀ i, evalPolynomial x.val (f i) ≠ 0 := Iff.rfl

private lemma evalPolynomial_finset_prod
    {ι : Type*} [Fintype ι] {σ : Type*} (x : σ → k)
    (f : ι → MvPolynomial σ k) :
    evalPolynomial x (∏ i, f i) = ∏ i, evalPolynomial x (f i) := by
  classical
  simp [evalPolynomial]

/-- A finite principal-open locus is Zariski open. -/
public theorem Variety.principalOpenLocus_isZariskiOpen
    {ι : Type*} [Fintype ι] (V : Variety k)
    (f : ι → MvPolynomial V.Coordinates k) :
    IsZariskiOpen V (V.principalOpenLocus f) := by
  classical
  rw [isZariskiOpen_iff]
  let p : MvPolynomial V.Coordinates k := ∏ i, f i
  refine ⟨{p}, ?_⟩
  ext x
  change (¬ ∀ i, evalPolynomial x.val (f i) ≠ 0) ↔
    ∀ q, q = p → evalPolynomial x.val q = 0
  simp only [not_forall, not_ne_iff]
  constructor
  · rintro ⟨i, hi⟩
    intro q hq
    subst q
    rw [show evalPolynomial x.val p = ∏ i, evalPolynomial x.val (f i) by
        dsimp [p]
        exact evalPolynomial_finset_prod x.val f]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  · intro hp
    have hp0 := hp p rfl
    rw [show evalPolynomial x.val p = ∏ i, evalPolynomial x.val (f i) by
        dsimp [p]
        exact evalPolynomial_finset_prod x.val f] at hp0
    simpa [Finset.prod_eq_zero_iff] using hp0

/-- Rational points of a principal open, as a subtype of the ambient point
space. -/
public abbrev Variety.PrincipalOpenPoint {ι : Type*} [Fintype ι]
    (V : Variety k) (f : ι → MvPolynomial V.Coordinates k) : Type u :=
  {x : Variety.Point V // x ∈ V.principalOpenLocus f}

namespace Variety.PrincipalOpenPoint

variable {ι : Type*} [Fintype ι]
variable {V : Variety k} {f : ι → MvPolynomial V.Coordinates k}

/-- Restriction of an ambient polynomial function to a principal open. -/
@[expose]
public def polynomialFunction (a : Variety.PolynomialFunction V) :
    Variety.PrincipalOpenPoint V f → k :=
  fun x => a x.1

@[simp] public theorem polynomialFunction_apply
    (a : Variety.PolynomialFunction V)
    (x : Variety.PrincipalOpenPoint V f) :
    polynomialFunction a x = a x.1 := rfl

/-- The regular function on a principal open represented by an ambient
polynomial. -/
@[expose]
public def regularFunction (p : MvPolynomial V.Coordinates k) :
    Variety.PrincipalOpenPoint V f → k :=
  fun x => evalPolynomial x.1.val p

@[simp] public theorem regularFunction_apply
    (p : MvPolynomial V.Coordinates k)
    (x : Variety.PrincipalOpenPoint V f) :
    regularFunction p x = evalPolynomial x.1.val p := rfl

/-- A quotient of two ambient polynomials, evaluated on a principal open.
The denominator hypothesis is part of the interface, so the definition is
usable without any global nonvanishing or reducedness assumptions. -/
@[expose]
public def rationalFunction (p q : MvPolynomial V.Coordinates k)
    (_hq : ∀ x : Variety.PrincipalOpenPoint V f,
      evalPolynomial x.1.val q ≠ 0) :
    Variety.PrincipalOpenPoint V f → k :=
  fun x => evalPolynomial x.1.val p / evalPolynomial x.1.val q

@[simp] public theorem rationalFunction_apply
    (p q : MvPolynomial V.Coordinates k)
    (hq : ∀ x : Variety.PrincipalOpenPoint V f,
      evalPolynomial x.1.val q ≠ 0)
    (x : Variety.PrincipalOpenPoint V f) :
    rationalFunction p q hq x =
      evalPolynomial x.1.val p / evalPolynomial x.1.val q := rfl

/-- The inverse of a selected polynomial is a rational function on the
principal open. -/
@[expose]
public noncomputable def selectedInverse (i : ι) : Variety.PrincipalOpenPoint V f → k :=
  rationalFunction (MvPolynomial.C 1) (f i) (fun x => x.2 i)

@[simp] public theorem selectedInverse_apply (i : ι)
    (x : Variety.PrincipalOpenPoint V f) :
    selectedInverse (f := f) i x =
      (evalPolynomial x.1.val (f i))⁻¹ := by
  simp [selectedInverse, rationalFunction, evalPolynomial, div_eq_mul_inv]

/-- Multiplying by the selected inverse recovers the numerator on the
principal open. -/
public theorem regularFunction_mul_selectedInverse
    (p : MvPolynomial V.Coordinates k) (i : ι)
    (x : Variety.PrincipalOpenPoint V f) :
    regularFunction (f := f) p x * selectedInverse (f := f) i x =
      evalPolynomial x.1.val p / evalPolynomial x.1.val (f i) := by
  rw [regularFunction_apply, selectedInverse_apply, div_eq_mul_inv]

/-- The selected denominator and its inverse cancel on the principal open. -/
public theorem selectedInverse_mul_regularFunction_selected
    (i : ι) (x : Variety.PrincipalOpenPoint V f) :
    selectedInverse (f := f) i x * regularFunction (f := f) (f i) x = 1 := by
  rw [selectedInverse_apply, regularFunction_apply]
  exact inv_mul_cancel₀ (x.2 i)

public theorem regularFunction_selected_mul_selectedInverse
    (i : ι) (x : Variety.PrincipalOpenPoint V f) :
    regularFunction (f := f) (f i) x * selectedInverse (f := f) i x = 1 := by
  rw [selectedInverse_apply, regularFunction_apply]
  exact mul_inv_cancel₀ (x.2 i)

end Variety.PrincipalOpenPoint

end Theory.AlgebraicGroup
