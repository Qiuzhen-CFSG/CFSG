module

public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint

/-!
# Quadratic coordinates for the Hermitian five-point module

The existing Hermitian isometry puts the determinant in the chosen minus
form over the Frobenius fixed field. That field has two elements, so its
anisotropic parameter is one. In coordinates `(a,b,x,y)` the form is
`ab + x² + xy + y²`. The binary word
`(b,a,a+b+y,a+b+x,a+b+x+y)` belongs to the five-point core and has exactly
this quadratic value. Its explicit inverse gives a linear equivalence.

Only identities on 16 or 32 binary vectors are checked by finite reduction.
The field comparison and the Hermitian isometry remain structural proofs.
Source: Aschbacher–Smith, K.3.1.2, printed p.454, and B.3, pp.83–84.
-/

open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open BinaryPermutation

public noncomputable section
namespace Representation.OrthogonalFourMinus.FivePoint.Construction
local instance : Algebra (ZMod 2) (fixedField 1) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space 1) :=
  Module.compHom (Space 1) (algebraMap (ZMod 2) (fixedField 1))

private def binaryEquiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (e : V ≃+ W) : V ≃ₗ[ZMod 2] W :=
  { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

private def scalarEquiv : ZMod 2 ≃+* fixedField 1 :=
  RingEquiv.ofBijective (algebraMap (ZMod 2) (fixedField 1))
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨(algebraMap (ZMod 2) (fixedField 1)).injective, by
      rw [card_fixedField]; simp⟩)

private lemma parameter_one : ClassicalOrthogonal.Minus.parameter (fixedField 1) = 1 := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h (scalarEquiv.symm (ClassicalOrthogonal.Minus.parameter (fixedField 1))) with h | h
  · have hz : ClassicalOrthogonal.Minus.parameter (fixedField 1) = 0 := by
      simpa using congrArg scalarEquiv h
    exact False.elim (ClassicalOrthogonal.Minus.parameter_spec (fixedField 1) 0 (by simp [hz]))
  · simpa using congrArg scalarEquiv h

private abbrev Four := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

private def minusCoordinates : ClassicalOrthogonal.Minus.Space (fixedField 1) 1 ≃+ Four :=
  ((LinearEquiv.funUnique (Fin 1) (fixedField 1) (fixedField 1 × fixedField 1)).toAddEquiv.prodCongr
    (AddEquiv.refl _)).trans
    ((scalarEquiv.symm.toAddEquiv.prodCongr scalarEquiv.symm.toAddEquiv).prodCongr
      (scalarEquiv.symm.toAddEquiv.prodCongr scalarEquiv.symm.toAddEquiv))

private def hermitianCoordinates : Space 1 ≃ₗ[ZMod 2] Four :=
  binaryEquiv ((hermitianMinusIsometry 1).toLinearEquiv.toAddEquiv.trans minusCoordinates)

private def word (v : Four) : Full (Fin 5) :=
  ![v.1.2, v.1.1, v.1.1 + v.1.2 + v.2.2,
    v.1.1 + v.1.2 + v.2.1, v.1.1 + v.1.2 + v.2.1 + v.2.2]

private lemma word_core (v : Four) : word v ∈ core (Fin 5) := by
  have h : ∀ v : Four, ∑ i, word v i = 0 := by decide
  exact h v

private def fourCore : Four ≃ₗ[ZMod 2] core (Fin 5) where
  toFun v := ⟨word v, word_core v⟩
  invFun w := ((w.val 1, w.val 0),
    (w.val 3 + w.val 1 + w.val 0, w.val 2 + w.val 1 + w.val 0))
  left_inv := by
    have h : ∀ v : Four,
        ((word v 1, word v 0), (word v 3 + word v 1 + word v 0,
          word v 2 + word v 1 + word v 0)) = v := by decide
    exact h
  right_inv := by
    intro w
    apply Subtype.ext
    have h : ∀ w : Full (Fin 5), (∑ i, w i) = 0 →
        word ((w 1, w 0), (w 3 + w 1 + w 0, w 2 + w 1 + w 0)) = w := by decide
    exact h w.val w.property
  map_add' := by
    intro v w
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [word] <;> ring
  map_smul' := by
    intro c v
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [word, mul_add]

private lemma fourCore_form (v : Four) :
    FiveGeometry.form (fourCore v) =
      v.1.1 * v.1.2 + v.2.1 ^ 2 + v.2.1 * v.2.2 + v.2.2 ^ 2 := by
  have h : ∀ v : Four, (∑ i : Fin 5, ∑ j : Fin 5 with i < j, word v i * word v j) =
      v.1.1 * v.1.2 + v.2.1 ^ 2 + v.2.1 * v.2.2 + v.2.2 ^ 2 := by decide
  exact h v

/-- Binary coordinates preserving the literal Hermitian determinant. -/
def coordinates : Space 1 ≃ₗ[ZMod 2] core (Fin 5) := hermitianCoordinates.trans fourCore

/-- The coordinate equivalence preserves the full determinant quadratic form. -/
theorem coordinates_form (v : Space 1) :
    form 1 v = algebraMap (ZMod 2) (fixedField 1) (FiveGeometry.form (coordinates v)) := by
  rw [coordinates, LinearEquiv.trans_apply, fourCore_form]
  rw [← (hermitianMinusIsometry 1).map_app v]
  change ClassicalOrthogonal.Minus.quadraticForm (fixedField 1) 2
    (hermitianMinusIsometry 1 v) = scalarEquiv _
  let x := hermitianMinusIsometry 1 v
  change ClassicalOrthogonal.Minus.quadraticForm (fixedField 1) 2 x =
    scalarEquiv (scalarEquiv.symm (x.1 0).1 * scalarEquiv.symm (x.1 0).2 +
      scalarEquiv.symm x.2.1 ^ 2 + scalarEquiv.symm x.2.1 * scalarEquiv.symm x.2.2 +
      scalarEquiv.symm x.2.2 ^ 2)
  simp only [ClassicalOrthogonal.Minus.quadraticForm,
    ClassicalOrthogonal.Minus.form_apply, ClassicalOrthogonal.Minus.plane_apply,
    parameter_one, one_mul, CharTwo.sub_eq_add,
    map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, add_assoc]
  congr 1
  exact Fin.sum_univ_one _

end Representation.OrthogonalFourMinus.FivePoint.Construction
