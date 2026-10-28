module

public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
import Mathlib.Tactic.Ring

/-!
# Positive roots in the hyperbolic special unitary group of degree four

The basis is (e₁,e₂,f₁,f₂), with Gram matrix [0,I;I,0]. The short
root parameters range over the full quadratic field; the long roots range
over its trace-zero subgroup. We verify their additive laws and all six
positive-root relations in the actual determinant-one unitary matrices.
These are the coordinates for the defining-prime covering calculation,
not an assertion that root lifts in a cover satisfy the same relations.

Source: the unitary convention in GLS3 §2.2 and the multiplier calculation
in §6.1, used in Aschbacher--Smith I.1.4(3), printed p.408.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime

open Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

/-- The actual hyperbolic SU₄, retaining the original field involution. -/
abbrev HyperbolicSU := (hyperbolicForm J).specialSubgroup

/-- Additive parameters for long unitary roots. -/
def traceZero : AddSubgroup F where
  carrier := {t | J.conj t = -t}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all [add_comm]
  neg_mem' := by intro x hx; simp_all

@[simp] theorem conj_traceZero (t : traceZero J) : J.conj (t : F) = -(t : F) :=
  t.property

/-- The Levi short root. -/
def shortMatrix (a : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,a,0,0; 0,1,0,0; 0,0,1,0; 0,0,-J.conj a,1]

/-- The highest long root. -/
def highMatrix (s : traceZero J) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,s,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

/-- The other short root; its two entries are conjugate negatives. -/
def middleMatrix (b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,b; 0,1,-J.conj b,0; 0,0,1,0; 0,0,0,1]

/-- The simple long root. -/
def longMatrix (t : traceZero J) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; 0,1,0,t; 0,0,1,0; 0,0,0,1]

private theorem short_det (a : F) : (shortMatrix J a).det = 1 := by
  rw [Matrix.det_succ_column_zero]
  simp [shortMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix]

private theorem high_det (s : traceZero J) : (highMatrix J s).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [highMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [highMatrix]

private theorem middle_det (b : F) : (middleMatrix J b).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [middleMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [middleMatrix]

private theorem long_det (t : traceZero J) : (longMatrix J t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [longMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [longMatrix]

private theorem short_unitary (a : F) :
    (hyperbolicForm J).conjTranspose (shortMatrix J a) * gram * shortMatrix J a = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortMatrix, hyperbolicForm, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, J.conj_involutive a]

private theorem high_unitary (s : traceZero J) :
    (hyperbolicForm J).conjTranspose (highMatrix J s) * gram * highMatrix J s = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [highMatrix, hyperbolicForm, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ]

private theorem middle_unitary (b : F) :
    (hyperbolicForm J).conjTranspose (middleMatrix J b) * gram * middleMatrix J b = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleMatrix, hyperbolicForm, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, J.conj_involutive b]

private theorem long_unitary (t : traceZero J) :
    (hyperbolicForm J).conjTranspose (longMatrix J t) * gram * longMatrix J t = gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMatrix, hyperbolicForm, gram, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Additive short-root parametrization in the literal special unitary group. -/
def shortRoot : Multiplicative F →* HyperbolicSU J where
  toFun a := ⟨GeneralLinearGroup.mkOfDetNeZero (shortMatrix J a.toAdd)
    (by rw [short_det]; exact one_ne_zero),
    by exact short_unitary J a.toAdd, by exact Units.ext (short_det J a.toAdd)⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shortMatrix]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change shortMatrix J (a.toAdd+b.toAdd) = shortMatrix J a.toAdd * shortMatrix J b.toAdd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shortMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

/-- Additive highest-root parametrization. -/
def highRoot : Multiplicative (traceZero J) →* HyperbolicSU J where
  toFun s := ⟨GeneralLinearGroup.mkOfDetNeZero (highMatrix J s.toAdd)
    (by rw [high_det]; exact one_ne_zero),
    by exact high_unitary J s.toAdd, by exact Units.ext (high_det J s.toAdd)⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [highMatrix]
  map_mul' s t := by
    apply Subtype.ext; apply Units.ext
    change highMatrix J (s.toAdd+t.toAdd) = highMatrix J s.toAdd * highMatrix J t.toAdd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [highMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

/-- Additive parametrization of the second short root. -/
def middleRoot : Multiplicative F →* HyperbolicSU J where
  toFun b := ⟨GeneralLinearGroup.mkOfDetNeZero (middleMatrix J b.toAdd)
    (by rw [middle_det]; exact one_ne_zero),
    by exact middle_unitary J b.toAdd, by exact Units.ext (middle_det J b.toAdd)⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [middleMatrix]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change middleMatrix J (a.toAdd+b.toAdd) = middleMatrix J a.toAdd * middleMatrix J b.toAdd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [middleMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

/-- Additive simple-long-root parametrization. -/
def longRoot : Multiplicative (traceZero J) →* HyperbolicSU J where
  toFun t := ⟨GeneralLinearGroup.mkOfDetNeZero (longMatrix J t.toAdd)
    (by rw [long_det]; exact one_ne_zero),
    by exact long_unitary J t.toAdd, by exact Units.ext (long_det J t.toAdd)⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longMatrix]
  map_mul' s t := by
    apply Subtype.ext; apply Units.ext
    change longMatrix J (s.toAdd+t.toAdd) = longMatrix J s.toAdd * longMatrix J t.toAdd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longMatrix, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

/-- The correction in the middle/short crossing is skew trace, not `-2ab`. -/
def skew (a b : F) : traceZero J :=
  ⟨a * J.conj b - b * J.conj a, by
    change J.conj _ = -_
    simp only [map_sub, map_mul, J.conj_involutive a, J.conj_involutive b]
    ring⟩

/-- The norm multiple occurring in the long/short crossing. -/
def normMul (a : F) (t : traceZero J) : traceZero J :=
  ⟨a * J.conj a * t, by
    change J.conj _ = -_
    simp only [map_mul, J.conj_involutive a, conj_traceZero]
    ring⟩

/-- The Levi short root commutes with the highest root. -/
theorem short_high_commute (a : F) (s : traceZero J) :
    Commute (shortRoot J (.ofAdd a)) (highRoot J (.ofAdd s)) := by
  change _ * _ = _ * _
  apply Subtype.ext; apply Units.ext
  change shortMatrix J a * highMatrix J s = highMatrix J s * shortMatrix J a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortMatrix, highMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two upper-block roots commute. -/
theorem high_middle_commute (s : traceZero J) (b : F) :
    Commute (highRoot J (.ofAdd s)) (middleRoot J (.ofAdd b)) := by
  change _ * _ = _ * _
  apply Subtype.ext; apply Units.ext
  change highMatrix J s * middleMatrix J b = middleMatrix J b * highMatrix J s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleMatrix, highMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem high_long_commute (s t : traceZero J) :
    Commute (highRoot J (.ofAdd s)) (longRoot J (.ofAdd t)) := by
  change _ * _ = _ * _
  apply Subtype.ext; apply Units.ext
  change highMatrix J s * longMatrix J t = longMatrix J t * highMatrix J s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMatrix, highMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem middle_long_commute (b : F) (t : traceZero J) :
    Commute (middleRoot J (.ofAdd b)) (longRoot J (.ofAdd t)) := by
  change _ * _ = _ * _
  apply Subtype.ext; apply Units.ext
  change middleMatrix J b * longMatrix J t = longMatrix J t * middleMatrix J b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMatrix, middleMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Moving a short Levi root past the middle root produces a skew trace. -/
theorem middle_short_crossing (b a : F) :
    middleRoot J (.ofAdd b) * shortRoot J (.ofAdd a) =
      shortRoot J (.ofAdd a) * highRoot J (.ofAdd (skew J a b)) *
        middleRoot J (.ofAdd b) := by
  apply Subtype.ext; apply Units.ext
  change middleMatrix J b * shortMatrix J a =
    shortMatrix J a * highMatrix J (skew J a b) * middleMatrix J b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortMatrix, middleMatrix, highMatrix, skew, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The long/short crossing retains both the norm and field-valued corrections. -/
theorem long_short_crossing (t : traceZero J) (a : F) :
    longRoot J (.ofAdd t) * shortRoot J (.ofAdd a) =
      shortRoot J (.ofAdd a) * highRoot J (.ofAdd (normMul J a t)) *
        middleRoot J (.ofAdd (-a * (t : F))) * longRoot J (.ofAdd t) := by
  apply Subtype.ext; apply Units.ext
  change longMatrix J t * shortMatrix J a = shortMatrix J a *
    highMatrix J (normMul J a t) * middleMatrix J (-a * (t : F)) * longMatrix J t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortMatrix, middleMatrix, highMatrix, longMatrix, normMul,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The subgroup generated by all four positive unitary root groups. -/
def positive : Subgroup (HyperbolicSU J) :=
  (shortRoot J).range ⊔ (highRoot J).range ⊔ (middleRoot J).range ⊔ (longRoot J).range

/-- A lift package records equations in the covering group, including the
unitary conjugations; its existence is a separate mathematical obligation. -/
structure PositiveRootLifts {E : Type*} [Group E] (f : E →* HyperbolicSU J) where
  short : Multiplicative F →* E
  high : Multiplicative (traceZero J) →* E
  middle : Multiplicative F →* E
  long : Multiplicative (traceZero J) →* E
  project_short : f.comp short = shortRoot J
  project_high : f.comp high = highRoot J
  project_middle : f.comp middle = middleRoot J
  project_long : f.comp long = longRoot J
  commute_short_high : ∀ a s, Commute (short (.ofAdd a)) (high (.ofAdd s))
  commute_high_middle : ∀ s b, Commute (high (.ofAdd s)) (middle (.ofAdd b))
  commute_high_long : ∀ s t, Commute (high (.ofAdd s)) (long (.ofAdd t))
  commute_middle_long : ∀ b t, Commute (middle (.ofAdd b)) (long (.ofAdd t))
  crossing_middle_short : ∀ b a,
    middle (.ofAdd b) * short (.ofAdd a) =
      short (.ofAdd a) * high (.ofAdd (skew J a b)) * middle (.ofAdd b)
  crossing_long_short : ∀ t a,
    long (.ofAdd t) * short (.ofAdd a) =
      short (.ofAdd a) * high (.ofAdd (normMul J a t)) *
        middle (.ofAdd (-a * (t : F))) * long (.ofAdd t)

/-- All six relations hold in the original matrix group. This is the identity
cover case only; it does not supply lifts in an arbitrary central extension. -/
def matrixRootLifts : PositiveRootLifts J (MonoidHom.id (HyperbolicSU J)) where
  short := shortRoot J
  high := highRoot J
  middle := middleRoot J
  long := longRoot J
  project_short := rfl
  project_high := rfl
  project_middle := rfl
  project_long := rfl
  commute_short_high := short_high_commute J
  commute_high_middle := high_middle_commute J
  commute_high_long := high_long_commute J
  commute_middle_long := middle_long_commute J
  crossing_middle_short := middle_short_crossing J
  crossing_long_short := long_short_crossing J

/-- Actual special-unitary transport, obtained from two orthonormal bases. -/
theorem exists_hyperbolic_special_equiv [Finite F] {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    Nonempty (HyperbolicSU J ≃* J.specialSubgroup) := by
  obtain ⟨C, e, _, _, _, _⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport J q hp hcard hconj
  obtain ⟨D, eh, _, _, _, _⟩ :=
    HermitianForm.IdentityGram.exists_identityGram_transport (hyperbolicForm J)
      q hp hcard hconj
  exact ⟨eh.trans e.symm⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
