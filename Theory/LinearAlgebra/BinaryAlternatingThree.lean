module
public import Theory.LinearAlgebra.BinaryAlternatingSevenLinear
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Odd prime actors on separating binary alternating forms in dimension three

An actor of order three or seven which preserves a family of alternating
forms with zero common radical is the identity. For order three, a
kernel-checked finite certificate finds a nonzero common radical vector
for every nonidentity actor. This vector is the fixed line. The existing
order-seven obstruction excludes a nonzero invariant alternating form.
Coordinates transfer the certificate to any three-dimensional binary space. No individual form is assumed
nondegenerate. This is the linear algebra of the class-two argument in
MacWilliams (1970), §3, pp.366–374.
-/
namespace BinaryAlternatingThree
open Matrix
private abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)
private def alternating (a b c : ZMod 2) : Mat := !![0,a,b; a,0,c; b,c,0]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
private theorem common_radical_certificate : ∀ A : Mat,
    A ^ 3 = 1 → A ≠ 1 →
    ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ ∀ a b c : ZMod 2,
      A.transpose * alternating a b c * A = alternating a b c →
        vecMul v (alternating a b c) = 0 := by
  decide

private theorem matrix_eq_alternating (B : Mat) (h : B.toBilin'.IsAlt) :
    B = alternating (B 0 1) (B 0 2) (B 1 2) := by
  have hd (i) : B i i = 0 := by
    simpa only [Matrix.toBilin'_single] using h.self_eq_zero (Pi.single i 1)
  have hs (i j) : B i j = B j i := by
    simpa only [Matrix.toBilin'_single, ZMod.neg_eq_self_mod_two] using
      h.neg_eq (Pi.single i 1) (Pi.single j 1)
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [alternating, hd] <;> first | rfl | exact hs _ _

/-- A separating family of alternating binary forms in dimension three
admits no nontrivial actor of order three or seven. -/
public theorem eq_one_of_separating_forms
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 3)
    (forms : Set (LinearMap.BilinForm (ZMod 2) V))
    (halt : ∀ B ∈ forms, B.IsAlt)
    (hsep : ∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0)
    (a : V ≃ₗ[ZMod 2] V) (hpow : a ^ 3 = 1 ∨ a ^ 7 = 1)
    (hpres : ∀ B ∈ forms, ∀ v w, B (a v) (a w) = B v w) : a = 1 := by
  classical
  rcases hpow with hpow | hpow
  swap
  · have hn : ∃ B ∈ forms, B ≠ 0 := by
      by_contra hn
      push Not at hn
      have hz (v : V) : v = 0 := hsep v (by
        intro B hB w
        rw [hn B hB]
        rfl)
      let : Subsingleton V := ⟨fun x y => (hz x).trans (hz y).symm⟩
      have hzdim := Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := V)
      omega
    obtain ⟨B, hB, hn⟩ := hn
    exact BinaryAlternatingFour.nonzero_alternating_form_order_seven_eq_one
      (by omega) B hn (halt B hB) a hpow (hpres B hB)
  let basis := Module.finBasisOfFinrankEq (ZMod 2) V hdim
  let e := basis.equivFun
  let matrixAut : (V ≃ₗ[ZMod 2] V) →* Mat :=
    LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp
      (e.conjRingEquiv.toMonoidHom.comp
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)))
  have hinj : Function.Injective matrixAut :=
    LinearMap.toMatrixAlgEquiv'.injective.comp
      (e.conjRingEquiv.injective.comp (fun _ _ h => LinearEquiv.toLinearMap_injective h))
  apply hinj
  rw [map_one]
  by_contra hn
  have hp : matrixAut a ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
  obtain ⟨v, hv, hrad⟩ := common_radical_certificate (matrixAut a) hp hn
  have hz : e.symm v = 0 := by
    apply hsep
    intro B hB w
    let C := B.comp e.symm.toLinearMap e.symm.toLinearMap
    have hC : C.toMatrix'.toBilin'.IsAlt := by
      rw [Matrix.toBilin'_toMatrix']
      exact fun x => halt B hB (e.symm x)
    have hCpres : (matrixAut a).transpose * C.toMatrix' * matrixAut a = C.toMatrix' := by
      change (e.conjRingEquiv a.toLinearMap).toMatrix'.transpose * C.toMatrix' *
        (e.conjRingEquiv a.toLinearMap).toMatrix' = _
      rw [← LinearMap.BilinForm.toMatrix'_comp]
      apply congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Fin 3 → ZMod 2) => B.toMatrix')
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      simpa [C, LinearEquiv.conjRingEquiv] using hpres B hB (e.symm x) (e.symm y)
    have hr : vecMul v C.toMatrix' = 0 := by
      rw [matrix_eq_alternating _ hC] at hCpres ⊢
      exact hrad _ _ _ hCpres
    have he : C v (e w) = 0 := by
      rw [← Matrix.toBilin'_toMatrix' C]
      rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, hr]
      simp
    simpa [C] using he
  apply hv
  simpa using congrArg e hz

end BinaryAlternatingThree
