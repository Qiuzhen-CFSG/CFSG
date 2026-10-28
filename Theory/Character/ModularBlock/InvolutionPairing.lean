module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Pairing invariant coefficients modulo an ideal

For an involution on a finite type, an invariant coefficient function whose
fixed-point coefficients lie in an ideal is a two-term orbit sum modulo
that ideal. There is no characteristic assumption and the ideal need not
contain two. This supplies the coefficient step of the order-two Brauer-kernel
relative-trace argument in the modular proof of Z-star.

Choose an ordering of the finite type and place the original coefficient
at the smaller point of each two-cycle. The two coefficients then sum to the
original value at every nonfixed point; at a fixed point their sum is zero,
so the remaining coefficient belongs to the ideal by hypothesis.

Ported from `Submission/ZStar/InvolutionPairing.lean` at revision `c3503435`
of `public/lean-eval/glauberman_zStar`, with the same statement.
-/

namespace ModularBlock.InvolutionPairing

attribute [local instance] Fintype.ofFinite

/-- An invariant finite coefficient function is an orbit sum modulo an ideal
when its fixed-point coefficients belong to that ideal. -/
public theorem exists_pairing_mod_ideal
    {R X : Type*} [Ring R] [Finite X]
    (tau : X → X) (htau : Function.Involutive tau)
    (I : Ideal R) (f : X →₀ R)
    (hinv : ∀ x, f (tau x) = f x)
    (hfixed : ∀ x, tau x = x → f x ∈ I) :
    ∃ b : X →₀ R, ∀ x, f x - (b x + b (tau x)) ∈ I := by
  let e := Fintype.equivFin X
  let : LinearOrder X := LinearOrder.lift' e e.injective
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
    simp

end ModularBlock.InvolutionPairing
