module

public import Theory.LinearAlgebra.BinaryAlternatingFourSeven
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Order-seven isometries of small binary alternating spaces

In dimension at most four, an isometry of a nonzero alternating binary form
whose seventh power is one must be the identity. The form need not be
nondegenerate. Add a complementary space with trivial actor and extend the
form by zero to obtain dimension four. Coordinates then reduce the claim to
the complete matrix obstruction, and restriction reflects the identity.

This is the linear-algebra input for the small 2-group commutator-form
argument in Stellmacher, printed p.42. The proof keeps the actual vector
space and actor and assumes no representation classification.
-/

open Matrix

namespace BinaryAlternatingFour

private theorem rank_four_order_seven_eq_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 4)
    (form : LinearMap.BilinForm (ZMod 2) V) (hne : form ≠ 0) (halt : form.IsAlt)
    (aut : V ≃ₗ[ZMod 2] V) (hpower : aut ^ 7 = 1)
    (hpres : ∀ left right, form (aut left) (aut right) = form left right) : aut = 1 := by
  classical
  let basis := Module.finBasisOfFinrankEq (ZMod 2) V hdim
  let coordinates := basis.equivFun
  let form' := form.comp coordinates.symm.toLinearMap coordinates.symm.toLinearMap
  let endAut := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)
  let matrixAut : (V ≃ₗ[ZMod 2] V) →* Mat :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
      (coordinates.conjRingEquiv.toMonoidHom.comp endAut)
  have hformNe : form' ≠ 0 := by
    intro hzero
    apply hne
    ext left right
    have heq := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) =>
      B (coordinates left) (coordinates right)) hzero
    simpa [form'] using heq
  have hformMatNe : form'.toMatrix' ≠ 0 := by
    simpa using hformNe
  have hformAlt : (form'.toMatrix').toBilin'.IsAlt := by
    rw [Matrix.toBilin'_toMatrix']
    intro point
    exact halt (coordinates.symm point)
  have hmatrixPow : matrixAut aut ^ 7 = 1 := by
    rw [← map_pow, hpower, map_one]
  have hmatrixPres : (matrixAut aut).transpose * form'.toMatrix' * matrixAut aut =
      form'.toMatrix' := by
    change (coordinates.conjRingEquiv aut.toLinearMap).toMatrix'.transpose *
      form'.toMatrix' * (coordinates.conjRingEquiv aut.toLinearMap).toMatrix' = _
    rw [← LinearMap.BilinForm.toMatrix'_comp]
    apply congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) => B.toMatrix')
    apply LinearMap.ext
    intro left
    apply LinearMap.ext
    intro right
    simpa [form', LinearEquiv.conjRingEquiv] using
      hpres (coordinates.symm left) (coordinates.symm right)
  have heq := nonzero_form_order_seven_eq_one form'.toMatrix' (matrixAut aut) hformMatNe hformAlt
    hmatrixPow hmatrixPres
  apply (LinearMap.toMatrixAlgEquiv'.injective.comp
    (coordinates.conjRingEquiv.injective.comp (show Function.Injective endAut from
      fun a b hab => LinearEquiv.toLinearMap_injective hab)))
  exact heq.trans matrixAut.map_one.symm

/-- A nonzero alternating binary form of dimension at most four admits no
nontrivial isometry whose seventh power is one. -/
public theorem nonzero_alternating_form_order_seven_eq_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V ≤ 4)
    (form : LinearMap.BilinForm (ZMod 2) V) (hne : form ≠ 0) (halt : form.IsAlt)
    (aut : V ≃ₗ[ZMod 2] V) (hpower : aut ^ 7 = 1)
    (hpres : ∀ left right, form (aut left) (aut right) = form left right) : aut = 1 := by
  classical
  let W := Fin (4 - Module.finrank (ZMod 2) V) → ZMod 2
  let fst : V × W →ₗ[ZMod 2] V := LinearMap.fst (ZMod 2) V W
  let extendedForm := form.comp fst fst
  let extend : (V ≃ₗ[ZMod 2] V) →* ((V × W) ≃ₗ[ZMod 2] (V × W)) :=
    { toFun := fun a => a.prodCongr (1 : W ≃ₗ[ZMod 2] W)
      map_one' := by ext <;> rfl
      map_mul' := by intros; ext <;> rfl }
  have hdimFour : Module.finrank (ZMod 2) (V × W) = 4 := by
    rw [Module.finrank_prod, Module.finrank_pi]
    simp only [Fintype.card_fin]
    omega
  have hformNe : extendedForm ≠ 0 := by
    intro hzero
    apply hne
    ext left right
    exact congrArg (fun B : LinearMap.BilinForm (ZMod 2) (V × W) =>
      B (left, 0) (right, 0)) hzero
  have hformAlt : extendedForm.IsAlt := fun point => halt point.1
  have hpow : extend aut ^ 7 = 1 := by rw [← map_pow, hpower, map_one]
  have hpres' : ∀ left right, extendedForm (extend aut left) (extend aut right) =
      extendedForm left right := fun left right => hpres left.1 right.1
  have heq := rank_four_order_seven_eq_one hdimFour extendedForm
    hformNe hformAlt (extend aut) hpow hpres'
  ext point
  exact congrArg (fun a : (V × W) ≃ₗ[ZMod 2] (V × W) => (a (point, 0)).1) heq

end BinaryAlternatingFour
