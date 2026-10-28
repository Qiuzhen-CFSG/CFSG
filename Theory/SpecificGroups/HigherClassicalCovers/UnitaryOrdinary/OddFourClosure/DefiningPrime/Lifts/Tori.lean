module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Roots
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Collection
public import Mathlib.Algebra.Ring.Action.End
import Mathlib.Tactic.Ring

/-!
# Fixed-field tori for the positive roots of SU₄

The matrices diag(a,b,a⁻¹,b⁻¹), for a,b in the fixed field, have determinant
one and preserve the actual hyperbolic Hermitian form. Their four weights
are a/b, a², ab, b². Multiplication by a fixed scalar preserves trace-zero
parameters. These literal identities supply the normalizers for constructing
root lifts and comparing lifted crossing relations.

Source: GLS3 §6.1, the defining-prime covering calculation underlying
Aschbacher--Smith I.1.4(3), printed p.408.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
open Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

/-- The literal fixed field of the stored involution. -/
abbrev fixedField := FixedBy.subfield F J.conj

/-- The coefficient in F of a unit of the fixed field. -/
def fixedUnitVal (a : (fixedField J)ˣ) : F := ((a : fixedField J) : F)

@[simp] theorem conj_fixed (a : fixedField J) : J.conj (a : F) = a := a.property
@[simp] theorem fixedUnitVal_one : fixedUnitVal J 1 = 1 := rfl
@[simp] theorem fixedUnitVal_mul (a b : (fixedField J)ˣ) :
    fixedUnitVal J (a*b) = fixedUnitVal J a * fixedUnitVal J b := rfl
@[simp] theorem fixedUnitVal_inv (a : (fixedField J)ˣ) :
    fixedUnitVal J a⁻¹ = (fixedUnitVal J a)⁻¹ := by simp [fixedUnitVal]
@[simp] theorem fixedUnitVal_pow (a : (fixedField J)ˣ) (n : ℕ) :
    fixedUnitVal J (a^n) = fixedUnitVal J a ^ n := rfl
@[simp] theorem fixedUnitVal_ne_zero (a : (fixedField J)ˣ) :
    fixedUnitVal J a ≠ 0 := by
  dsimp [fixedUnitVal]
  exact_mod_cast a.ne_zero
@[simp] theorem conj_fixedUnitVal (a : (fixedField J)ˣ) :
    J.conj (fixedUnitVal J a) = fixedUnitVal J a := (a : fixedField J).property

theorem fixedUnitVal_injective : Function.Injective (fixedUnitVal J) := by
  intro a b h
  exact Units.ext (Subtype.ext h)

/-- Fixed scalars act additively on the long-root parameters. -/
def scaleTrace (c : fixedField J) : traceZero J →+ traceZero J where
  toFun t := ⟨(c : F) * t, by
    change J.conj _ = -_
    rw [map_mul, conj_fixed, conj_traceZero, mul_neg]⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' s t := Subtype.ext (mul_add _ _ _)

@[simp] theorem coe_scaleTrace (c : fixedField J) (t : traceZero J) :
    (scaleTrace J c t : F) = (c : F) * t := rfl
@[simp] theorem scaleTrace_one (t : traceZero J) : scaleTrace J 1 t = t :=
  Subtype.ext (one_mul _)
@[simp] theorem scaleTrace_mul (c d : fixedField J) (t : traceZero J) :
    scaleTrace J (c*d) t = scaleTrace J c (scaleTrace J d t) :=
  Subtype.ext (mul_assoc _ _ _)

def fixedDiagonalMatrix (a b : (fixedField J)ˣ) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.diagonal ![fixedUnitVal J a, fixedUnitVal J b,
    fixedUnitVal J a⁻¹, fixedUnitVal J b⁻¹]

private theorem fixedDiagonal_det (a b : (fixedField J)ˣ) :
    (fixedDiagonalMatrix J a b).det = 1 := by
  simp [fixedDiagonalMatrix, Matrix.det_diagonal, Fin.prod_univ_succ,
    mul_comm, mul_left_comm]

private theorem fixedDiagonal_unitary (a b : (fixedField J)ˣ) :
    (hyperbolicForm J).conjTranspose (fixedDiagonalMatrix J a b) * gram *
      fixedDiagonalMatrix J a b = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDiagonalMatrix, hyperbolicForm, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- A determinant-one unitary diagonal torus, not an abstract torus label. -/
def fixedDiagonal (a b : (fixedField J)ˣ) : HyperbolicSU J :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (fixedDiagonalMatrix J a b)
    (by rw [fixedDiagonal_det]; exact one_ne_zero),
    by exact fixedDiagonal_unitary J a b, by exact Units.ext (fixedDiagonal_det J a b)⟩

theorem fixedDiagonal_commute (a b c d : (fixedField J)ˣ) :
    Commute (fixedDiagonal J a b) (fixedDiagonal J c d) := by
  change _ * _ = _ * _
  apply Subtype.ext; apply Units.ext
  change fixedDiagonalMatrix J a b * fixedDiagonalMatrix J c d =
    fixedDiagonalMatrix J c d * fixedDiagonalMatrix J a b
  simp only [fixedDiagonalMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem fixedDiagonal_short (a b : (fixedField J)ˣ) (x : F) :
    fixedDiagonal J a b * shortRoot J (.ofAdd x) * (fixedDiagonal J a b)⁻¹ =
      shortRoot J (.ofAdd (fixedUnitVal J (a*b⁻¹) * x)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext; apply Units.ext
  change fixedDiagonalMatrix J a b * shortMatrix J x =
    shortMatrix J (fixedUnitVal J (a*b⁻¹)*x) * fixedDiagonalMatrix J a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDiagonalMatrix, shortMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_assoc, mul_comm, mul_left_comm]

theorem fixedDiagonal_high (a b : (fixedField J)ˣ) (s : traceZero J) :
    fixedDiagonal J a b * highRoot J (.ofAdd s) * (fixedDiagonal J a b)⁻¹ =
      highRoot J (.ofAdd (scaleTrace J ((a : fixedField J)^2) s)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext; apply Units.ext
  change fixedDiagonalMatrix J a b * highMatrix J s =
    highMatrix J (scaleTrace J ((a : fixedField J)^2) s) * fixedDiagonalMatrix J a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDiagonalMatrix, highMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      fixedUnitVal, pow_two, mul_assoc, mul_comm, mul_left_comm]

theorem fixedDiagonal_middle (a b : (fixedField J)ˣ) (x : F) :
    fixedDiagonal J a b * middleRoot J (.ofAdd x) * (fixedDiagonal J a b)⁻¹ =
      middleRoot J (.ofAdd (fixedUnitVal J (a*b) * x)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext; apply Units.ext
  change fixedDiagonalMatrix J a b * middleMatrix J x =
    middleMatrix J (fixedUnitVal J (a*b)*x) * fixedDiagonalMatrix J a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDiagonalMatrix, middleMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_assoc, mul_comm]

theorem fixedDiagonal_long (a b : (fixedField J)ˣ) (s : traceZero J) :
    fixedDiagonal J a b * longRoot J (.ofAdd s) * (fixedDiagonal J a b)⁻¹ =
      longRoot J (.ofAdd (scaleTrace J ((b : fixedField J)^2) s)) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext; apply Units.ext
  change fixedDiagonalMatrix J a b * longMatrix J s =
    longMatrix J (scaleTrace J ((b : fixedField J)^2) s) * fixedDiagonalMatrix J a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedDiagonalMatrix, longMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      fixedUnitVal, pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- Cardinality of the actual coefficient field used by the torus. -/
theorem card_fixedField [Finite F] {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    Nat.card (fixedField J) = q := by
  let : Fact q.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact J.card_fixed_of_prime_frobenius hconj

/-- Four additive sections with the torus actions fixed. Cross-root relations
are deliberately absent: proving them is a separate compatibility calculation. -/
structure EquivariantRootLifts {E : Type*} [Group E] (f : E →* HyperbolicSU J) where
  short : Multiplicative F →* E
  high : Multiplicative (traceZero J) →* E
  middle : Multiplicative F →* E
  long : Multiplicative (traceZero J) →* E
  project_short : f.comp short = shortRoot J
  project_high : f.comp high = highRoot J
  project_middle : f.comp middle = middleRoot J
  project_long : f.comp long = longRoot J
  equiv_short : ∀ (a b : (fixedField J)ˣ) (z : E), f z = fixedDiagonal J a b →
    ∀ x : F, z * short (.ofAdd x) * z⁻¹ = short (.ofAdd (fixedUnitVal J (a*b⁻¹)*x))
  equiv_high : ∀ (a b : (fixedField J)ˣ) (z : E), f z = fixedDiagonal J a b →
    ∀ s : traceZero J, z * high (.ofAdd s) * z⁻¹ =
      high (.ofAdd (scaleTrace J ((a : fixedField J)^2) s))
  equiv_middle : ∀ (a b : (fixedField J)ˣ) (z : E), f z = fixedDiagonal J a b →
    ∀ x : F, z * middle (.ofAdd x) * z⁻¹ = middle (.ofAdd (fixedUnitVal J (a*b)*x))
  equiv_long : ∀ (a b : (fixedField J)ˣ) (z : E), f z = fixedDiagonal J a b →
    ∀ s : traceZero J, z * long (.ofAdd s) * z⁻¹ =
      long (.ofAdd (scaleTrace J ((b : fixedField J)^2) s))

/-- The matrix roots satisfy the new equivariance interface literally. This
is the identity map application of the torus calculation, not a lift through
an arbitrary covering group. -/
def matrixEquivariantRootLifts :
    EquivariantRootLifts J (MonoidHom.id (HyperbolicSU J)) where
  short := shortRoot J
  high := highRoot J
  middle := middleRoot J
  long := longRoot J
  project_short := rfl
  project_high := rfl
  project_middle := rfl
  project_long := rfl
  equiv_short := by intro a b z hz x; change z = _ at hz; subst z; exact fixedDiagonal_short J a b x
  equiv_high := by intro a b z hz s; change z = _ at hz; subst z; exact fixedDiagonal_high J a b s
  equiv_middle := by intro a b z hz x; change z = _ at hz; subst z; exact fixedDiagonal_middle J a b x
  equiv_long := by intro a b z hz s; change z = _ at hz; subst z; exact fixedDiagonal_long J a b s

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
