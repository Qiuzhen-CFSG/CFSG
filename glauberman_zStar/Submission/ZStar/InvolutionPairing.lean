import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Pairing coefficients along the two-cycles of an involution.

This is the elementary coefficient step behind the order-two Brauer-kernel
argument: away from the fixed points, an invariant coefficient function is
an exact relative trace; at fixed points the remaining error is whatever was
already present there.
-/

noncomputable section

namespace Submission.ZStar
namespace InvolutionPairing

universe u v

attribute [local instance] Fintype.ofFinite

theorem exists_pairing_mod_ideal
    {R X : Type*} [Ring R] [Finite X]
    (tau : X → X) (htau : Function.Involutive tau)
    (I : Ideal R) (f : X →₀ R)
    (hinv : ∀ x, f (tau x) = f x)
    (hfixed : ∀ x, tau x = x → f x ∈ I) :
    ∃ b : X →₀ R, ∀ x, f x - (b x + b (tau x)) ∈ I := by
  let e := Fintype.equivFin X
  letI : LinearOrder X := LinearOrder.lift' e e.injective
  let b : X →₀ R := Finsupp.equivFunOnFinite.symm
    (fun x => if x < tau x then f x else 0)
  refine ⟨b, fun x => ?_⟩
  have hb (y : X) : b y = if y < tau y then f y else 0 := by
    simp [b]
  rcases lt_trichotomy x (tau x) with hlt | heq | hgt
  · have hnlt : ¬tau x < x := not_lt_of_ge hlt.le
    rw [hb x, hb (tau x), if_pos hlt]
    simp only [htau x, if_neg hnlt, add_zero, sub_self]
    exact I.zero_mem
  · have htaux : tau x = x := heq.symm
    have hfx : f x ∈ I := hfixed x htaux
    rw [hb x, hb (tau x), htaux]
    simpa [htaux] using hfx
  · have hnlt : ¬x < tau x := not_lt_of_ge hgt.le
    have hlt' : tau x < tau (tau x) := by simpa [htau x] using hgt
    rw [hb x, hb (tau x), if_neg hnlt, if_pos hlt']
    rw [hinv x]
    simpa using I.zero_mem

end InvolutionPairing
end Submission.ZStar
