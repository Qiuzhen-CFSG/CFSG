/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFAppendixIII.lemma_2
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Peterfalvi Appendix III, Proposition 1
-/

namespace BenderSuzuki
namespace PFAppendixIII

universe u

/-- Appendix III, Proposition 1. The anisotropic quadratic form
`a^2 + epsilon * a * b + b^2` on `F x F` is the norm of a quadratic field
extension of `F`, expressed through a linear equivalence with `F x F`. -/
public theorem proposition1_quadraticForm_is_quadraticFieldNorm
    (F : Type u) [Field F] [Fintype F] [CharP F 2]
    (epsilon : F)
    (hanisotropic :
      ∀ a b : F, (a, b) ≠ (0, 0) →
        a ^ 2 + epsilon * a * b + b ^ 2 ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E)
        (coordinates : (F × F) ≃ₗ[F] E)
        (conjugation : E ≃ₐ[F] E),
      orderOf conjugation = 2 ∧
        ∀ a b : F,
          coordinates (a, b) * conjugation (coordinates (a, b)) =
            algebraMap F E (a ^ 2 + epsilon * a * b + b ^ 2) := by
  classical
  have hno_root (r : F) : r ^ 2 ≠ (1 : F) + epsilon * r := by
    intro hr
    exact (hanisotropic r 1 (by simp)) (by
      rw [hr]
      ring_nf
      simp [CharTwo.two_eq_zero])
  letI : Fact (∀ r : F, r ^ 2 ≠ (1 : F) + epsilon * r) :=
    ⟨hno_root⟩
  have hepsilon_ne : epsilon ≠ 0 := by
    intro hepsilon
    exact (hanisotropic 1 1 (by simp)) (by
      simp only [hepsilon, zero_mul, add_zero, one_pow]
      simpa only [one_add_one_eq_two] using
        (CharTwo.two_eq_zero (R := F)))
  let coordinates : (F × F) ≃ₗ[F] QuadraticAlgebra F 1 epsilon :=
    (LinearEquiv.finTwoArrow F F).symm.trans
      (QuadraticAlgebra.linearEquivTuple (1 : F) epsilon).symm
  have hcoordinates_apply (a b : F) :
      coordinates (a, b) =
        (⟨a, b⟩ : QuadraticAlgebra F 1 epsilon) := by
    rfl
  let conjugation : QuadraticAlgebra F 1 epsilon ≃ₐ[F]
      QuadraticAlgebra F 1 epsilon :=
    AlgEquiv.ofRingEquiv
      (f := (starRingAut : RingAut (QuadraticAlgebra F 1 epsilon))) (by
        intro x
        ext <;> simp)
  have hconjugation_apply (z : QuadraticAlgebra F 1 epsilon) :
      conjugation z = star z := by
    rfl
  have hconjugation_sq : conjugation ^ 2 = 1 := by
    apply DFunLike.ext _ _
    intro z
    change conjugation (conjugation z) = z
    rw [hconjugation_apply, hconjugation_apply]
    exact star_star z
  have hconjugation_ne_one : conjugation ≠ 1 := by
    intro hconjugation
    have hstar :
        star (QuadraticAlgebra.omega : QuadraticAlgebra F 1 epsilon) =
          QuadraticAlgebra.omega := by
      rw [← hconjugation_apply]
      simpa using DFunLike.congr_fun hconjugation
        (QuadraticAlgebra.omega : QuadraticAlgebra F 1 epsilon)
    apply hepsilon_ne
    simpa only [QuadraticAlgebra.re_star, QuadraticAlgebra.omega_re,
      QuadraticAlgebra.omega_im, zero_add, mul_one] using
      congrArg (fun z : QuadraticAlgebra F 1 epsilon => z.re) hstar
  have horder : orderOf conjugation = 2 :=
    orderOf_eq_prime hconjugation_sq hconjugation_ne_one
  have hnorm (a b : F) :
      coordinates (a, b) * conjugation (coordinates (a, b)) =
        algebraMap F (QuadraticAlgebra F 1 epsilon)
          (a ^ 2 + epsilon * a * b + b ^ 2) := by
    rw [hcoordinates_apply, hconjugation_apply,
      ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simp [QuadraticAlgebra.norm_def, CharTwo.sub_eq_add, pow_two]
  exact ⟨QuadraticAlgebra F 1 epsilon, inferInstance, inferInstance,
    coordinates, conjugation, horder, hnorm⟩

end PFAppendixIII
end BenderSuzuki
