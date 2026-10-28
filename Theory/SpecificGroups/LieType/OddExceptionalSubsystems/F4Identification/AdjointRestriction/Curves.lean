module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Coordinates
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Scalar extension of the folded adjoint comparison

These matrix curves are the exact signed generators of `coverEvaluation`
and `foldedEvaluation`, with the existing F4 node reversal and the original
parameter. An intertwining identity over `ℤ[X]` specializes to every
commutative coefficient ring by evaluating `X` at that parameter. In
particular this step divides by neither two nor three and remains valid
in characteristic three.

The integral polynomial identity remains an explicit hypothesis. This file
identifies its concrete matrices and proves its application to the literal
column actions; it does not assert the missing identity.

Sources: GLS3 §§2.2--2.6 and the integral Geck divided-power curves; the
F4 inclusions in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
open Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- The polynomial source simple-root curve, before taking units or subgroups. -/
def sourceCurve (R : Type*) [CommRing R] (s : Bool) (i : Fin 4) (t : R) :
    Matrix SourceIndex SourceIndex R :=
  (simpleFamily (b := typeF4RootPairing_base)).curve (s, sourceIndex i) t

/-- The literal E6 simple-root curve as a matrix over any commutative ring. -/
def targetCurve (R : Type*) [CommRing R] (s : Bool) (i : Fin 6) (t : R) :
    Matrix TwistedE6.Index TwistedE6.Index R :=
  (simpleFamily (b := TwistedE6.Base)).curve (s, simpleIndex i) t

/-- The paired E6 polynomial curves, in the same F4 numbering as `f4Simple`. -/
def foldedCurve (R : Type*) [CommRing R] (s : Bool) (i : Fin 4) (t : R) :
    Matrix TwistedE6.Index TwistedE6.Index R :=
  ![targetCurve R s 0 t * targetCurve R s 5 t,
    targetCurve R s 1 t * targetCurve R s 4 t,
    targetCurve R s 2 t, targetCurve R s 3 t] i.rev

@[simp] theorem map_matrix {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (matrix R).map f = matrix S := by
  ext i j
  exact map_intCast f _

@[simp] theorem map_sourceCurve {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Bool) (i : Fin 4) (t : R) :
    (sourceCurve R s i t).map f = sourceCurve S s i (f t) :=
  IntegralCubicFamily.map_curve _ f _ t

@[simp] theorem map_targetCurve {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Bool) (i : Fin 6) (t : R) :
    (targetCurve R s i t).map f = targetCurve S s i (f t) :=
  IntegralCubicFamily.map_curve _ f _ t

@[simp] theorem map_foldedCurve {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Bool) (i : Fin 4) (t : R) :
    (foldedCurve R s i t).map f = foldedCurve S s i (f t) := by
  fin_cases i <;> simp [foldedCurve, Matrix.map_mul, Fin.rev]

/-- Polynomial evaluation specializes an integral identity without division by factorials. -/
theorem curve_intertwines_of_integral_polynomial (R : Type*) [CommRing R]
    (h : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (s : Bool) (i : Fin 4) (t : R) :
    foldedCurve R s i t * matrix R = matrix R * sourceCurve R s i t := by
  let ev : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have hh := congrArg (fun A => Matrix.map A ev) (h s i)
  simp only [Matrix.map_mul, map_matrix, map_sourceCurve, map_foldedCurve] at hh
  simpa only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hh

variable (F : Type*) [Field F]

@[simp] theorem coverSimple_matrix (s : Bool) (i : Fin 4) (t : F) :
    (coverSimple F s i t).val.val = sourceCurve F s i t := by
  rw [coverSimple_val]
  rfl

@[simp] theorem f4Simple_matrix (s : Bool) (i : Fin 4) (t : F) :
    (f4Simple F s i t).val.val.val = foldedCurve F s i t := by
  fin_cases i <;>
    simp [f4Simple, foldedSimple, foldedCurve, Fin.rev, Subgroup.coe_mul, Units.val_mul,
      targetCurve]

/-- Specialization acts on columns with the original sign, node and parameter. -/
theorem simple_mulVec_intertwines_of_integral_polynomial
    (hpoly : ∀ s i,
      foldedCurve (Polynomial ℤ) s i Polynomial.X * matrix (Polynomial ℤ) =
        matrix (Polynomial ℤ) * sourceCurve (Polynomial ℤ) s i Polynomial.X)
    (s : Bool) (i : Fin 4) (t : F) (x : SourceIndex → F) :
    (f4Simple F s i t).val.val.val *ᵥ linearMap F x =
      linearMap F ((coverSimple F s i t).val.val *ᵥ x) := by
  simp only [f4Simple_matrix, coverSimple_matrix, linearMap, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, curve_intertwines_of_integral_polynomial F hpoly]

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
