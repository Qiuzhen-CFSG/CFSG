module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Finite-field units for the twisted cubic G₂ torus

Let K/F be quadratic and E/K cubic, with |F| = p. The subgroup of Eˣ
annihilated by p² − p + 1 is cyclic of precisely that order. The identities
(p² − p + 1)(p + 1) = p³ + 1 and
(p² − p + 1)(p² + p + 1) = p⁴ + p² + 1 show that its elements have
Hermitian norm one and determinant one in the regular representation over K.
We construct that faithful SL₃ representation and prove that its actual
multiplication action preserves the nondegenerate trace pairing.

The passage to a standard SU₃ and its faithful octonion embedding are not
asserted here. `TwistedCubicTorus` supplies their precise conditional
Sylow and universal-cover applications, retaining both missing maps.
In particular no projective quotient is taken, so the full prime powers
in the torus order are retained.

Source application: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408,
and GLS III §6.1. This is the finite-field construction needed for the
unitary subsystem route to the twisted torus, not a proof of those full
multiplier statements.
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus

open Matrix
open scoped MatrixGroups

noncomputable section
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The chosen quadratic extension of the coefficient field. -/
abbrev Quadratic := FiniteField.Extension F p 2
instance quadraticCharP : CharP (Quadratic F p) p :=
  charP_of_injective_algebraMap (algebraMap F (Quadratic F p)).injective p

/-- The chosen cubic extension of the quadratic field. -/
abbrev Sextic := FiniteField.Extension (Quadratic F p) p 3

instance sexticCharP : CharP (Sextic F p) p :=
  charP_of_injective_algebraMap (algebraMap (Quadratic F p) (Sextic F p)).injective p

/-- All roots of unity of the full twisted cyclotomic order. -/
def fieldUnits : Subgroup (Sextic F p)ˣ :=
  (powMonoidHom (p ^ 2 - p + 1) : (Sextic F p)ˣ →* (Sextic F p)ˣ).ker

instance : IsCyclic (fieldUnits F p) := inferInstanceAs (IsCyclic ((powMonoidHom (p ^ 2 - p + 1) :
  (Sextic F p)ˣ →* (Sextic F p)ˣ).ker))

theorem fieldUnits_pow (u : fieldUnits F p) : u.val ^ (p ^ 2 - p + 1) = 1 :=
  u.property

private theorem twisted_mul_linear (q : ℕ) :
    (q ^ 2 - q + 1) * (q + 1) = q ^ 3 + 1 := by
  have h : q ≤ q ^ 2 := by nlinarith
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub h]
  ring

private theorem twisted_mul_cubic (q : ℕ) :
    (q ^ 2 - q + 1) * (q ^ 2 + q + 1) = q ^ 4 + q ^ 2 + 1 := by
  have h : q ≤ q ^ 2 := by nlinarith
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub h]
  ring

private theorem cubic_factorization (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub hq, Nat.cast_sub (Nat.one_le_pow 3 q hq)]
  ring

theorem card_quadratic (hF : Nat.card F = p) : Nat.card (Quadratic F p) = p ^ 2 := by
  rw [FiniteField.natCard_extension, hF]

theorem card_sextic (hF : Nat.card F = p) : Nat.card (Sextic F p) = p ^ 6 := by
  rw [FiniteField.natCard_extension, card_quadratic F p hF, ← pow_mul]

/-- The full order, including its prime-power factors. -/
theorem card_fieldUnits (hF : Nat.card F = p) :
    Nat.card (fieldUnits F p) = p ^ 2 - p + 1 := by
  rw [fieldUnits, IsCyclic.card_powMonoidHom_ker, Nat.card_units, card_sextic F p hF]
  apply Nat.gcd_eq_right_iff_dvd.mpr
  refine dvd_trans ⟨p ^ 2 + p + 1, (twisted_mul_cubic p).symm⟩ ?_
  have hp : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (Fact.out : p.Prime).one_le
  have he := cubic_factorization (p ^ 2) hp
  rw [← pow_mul] at he
  rw [he]
  convert dvd_mul_left ((p ^ 2) ^ 2 + p ^ 2 + 1) (p ^ 2 - 1) using 1
  simp only [← pow_mul]

/-- Norm one for the involution raising to the p³-th power. -/
theorem fieldUnits_unitary (u : fieldUnits F p) :
    (u.val : Sextic F p) ^ (p ^ 3) * (u.val : Sextic F p) = 1 := by
  have h : u.val ^ (p ^ 3 + 1) = 1 := by
    rw [← twisted_mul_linear, pow_mul, fieldUnits_pow, one_pow]
  simpa only [pow_add, pow_one, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_one] using congrArg Units.val h

/-- Norm one to the quadratic field gives determinant one over that field. -/
theorem fieldUnits_norm (hF : Nat.card F = p) (u : fieldUnits F p) :
    Algebra.norm (Quadratic F p) (u.val : Sextic F p) = 1 := by
  apply (algebraMap (Quadratic F p) (Sextic F p)).injective
  rw [map_one, FiniteField.algebraMap_norm_eq_pow,
    FiniteField.natCard_extension, card_quadratic F p hF]
  have hp : 1 < p ^ 2 := by have := (Fact.out : p.Prime).two_le; nlinarith
  rw [cubic_factorization (p ^ 2) (by omega), Nat.mul_div_cancel_left _ (by omega)]
  have he : (p ^ 2) ^ 2 + p ^ 2 + 1 = (p ^ 2 - p + 1) * (p ^ 2 + p + 1) := by
    rw [← pow_mul]
    exact (twisted_mul_cubic p).symm
  rw [he, pow_mul]
  have hu : (u.val : Sextic F p) ^ (p ^ 2 - p + 1) = 1 :=
    congrArg Units.val (fieldUnits_pow F p u)
  rw [hu, one_pow]

/-- A basis of the cubic extension over the quadratic field. -/
def regularBasis : Module.Basis (Fin 3) (Quadratic F p) (Sextic F p) :=
  Module.finBasisOfFinrankEq _ _ (FiniteField.finrank_extension (Quadratic F p) p 3)

/-- The actual determinant-one regular multiplication representation. -/
def regularHom (hF : Nat.card F = p) : fieldUnits F p →* SL(3, Quadratic F p) where
  toFun u := ⟨Algebra.leftMulMatrix (regularBasis F p) (u.val : Sextic F p), by
    rw [← Algebra.norm_eq_matrix_det]
    exact fieldUnits_norm F p hF u⟩
  map_one' := by apply Subtype.ext; exact map_one (Algebra.leftMulMatrix (regularBasis F p))
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (Algebra.leftMulMatrix (regularBasis F p)) _ _

theorem regularHom_injective (hF : Nat.card F = p) :
    Function.Injective (regularHom F p hF) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact Algebra.leftMulMatrix_injective (regularBasis F p) (congrArg Subtype.val h)



/-- The faithful SL₃ action is literally multiplication in the sextic field. -/
theorem regularHom_mulVec_repr (hF : Nat.card F = p) (u : fieldUnits F p)
    (x : Sextic F p) :
    (regularHom F p hF u).val *ᵥ (regularBasis F p).repr x =
      (regularBasis F p).repr ((u.val : Sextic F p) * x) :=
  Algebra.leftMulMatrix_mulVec_repr (regularBasis F p) _ _

/-- The order-two automorphism of the sextic field over its cubic subfield. -/
def sexticConj : Sextic F p ≃+* Sextic F p :=
  (frobeniusEquiv (Sextic F p) p).trans
    ((frobeniusEquiv (Sextic F p) p).trans (frobeniusEquiv (Sextic F p) p))

theorem sexticConj_apply (x : Sextic F p) : sexticConj F p x = x ^ (p ^ 3) := by
  change ((x ^ p) ^ p) ^ p = _
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

theorem sexticConj_involutive (hF : Nat.card F = p) :
    Function.Involutive (sexticConj F p) := by
  intro x
  rw [sexticConj_apply, sexticConj_apply, ← pow_mul, ← pow_add]
  change x ^ (p ^ 6) = x
  rw [← card_sextic F p hF]
  let := Fintype.ofFinite (Sextic F p)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The trace pairing for the unitary regular representation. -/
def tracePairing (x y : Sextic F p) : Quadratic F p :=
  Algebra.trace (Quadratic F p) (Sextic F p) (sexticConj F p x * y)

theorem tracePairing_preserved (u : fieldUnits F p) (x y : Sextic F p) :
    tracePairing F p ((u.val : Sextic F p) * x) ((u.val : Sextic F p) * y) =
      tracePairing F p x y := by
  unfold tracePairing
  rw [(sexticConj F p).map_mul]
  have h := fieldUnits_unitary F p u
  rw [← sexticConj_apply] at h
  congr 1
  calc
    _ = (sexticConj F p (u.val : Sextic F p) * (u.val : Sextic F p)) *
      (sexticConj F p x * y) := by ring
    _ = _ := by rw [h, one_mul]

theorem tracePairing_nondegenerate_left (x : Sextic F p)
    (hx : ∀ y, tracePairing F p x y = 0) : x = 0 := by
  have h := (traceForm_nondegenerate (Quadratic F p) (Sextic F p)).1
    (sexticConj F p x) hx
  exact (sexticConj F p).injective (h.trans (map_zero _).symm)

end
end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
