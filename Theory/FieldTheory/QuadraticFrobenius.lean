module

public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The unique involution of a quadratic finite field

The Frobenius automorphism has order equal to the degree over the prime
field. In degree two the complete automorphism group has order two, so
its unique nonidentity element is this actual Frobenius. This identifies
the coefficient action in the square-field branch of Aschbacher--Smith
F.6.18(8), printed p.310.
-/

public noncomputable section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem frobeniusEquiv_orderOf_of_card {n : ℕ} (hcard : Nat.card F = p ^ n) :
    orderOf (frobeniusEquiv F p) = n := by
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let f : (F ≃ₐ[ZMod p] F) →* (F ≃+* F) := {
    toFun := AlgEquiv.toRingEquiv
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h => AlgEquiv.ext fun x =>
    DFunLike.congr_fun h x
  have he : f (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) =
      frobeniusEquiv F p := by
    ext x
    change x ^ Fintype.card (ZMod p) = x ^ p
    rw [ZMod.card]
  rw [← he, orderOf_injective f hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)).symm.trans hcard

theorem involution_eq_frobenius_of_card_square
    (hcard : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    σ = frobeniusEquiv F p := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : IsCyclic (F ≃+* F) := isCyclic_of_prime_card
    (FiniteField.card_ringAut_of_card_prime_pow (Fact.out : p.Prime) hcard)
  exact IsCyclic.eq_of_orderOf_eq_two hσ (frobeniusEquiv_orderOf_of_card hcard)

end FiniteField
