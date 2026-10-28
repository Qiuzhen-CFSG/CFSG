module
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases

/-!
# The factor swap and its order-five conjugate product

Adjugation interchanges the two special linear factors in their literal
left-right matrix action. For any a in SL₂(4), its product with its conjugate
by (a,1) is the matrix actor (a,a⁻¹), hence has order `orderOf a`.
The explicit matrix with rows (0,1), (1,ω) has order five. Conjugation
transports this obstruction to every conjugate of the swap.

Source: Aschbacher–Smith, G.11.2(7), printed p.364 (PDF p.375), and the
proof of 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public noncomputable section
namespace Representation.RankTwo.OrthogonalFour
open ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Module

/-- Adjugation is the outer involution interchanging the two special linear factors. -/
def swap : V ≃ₗ[F] V where
  toFun := Matrix.adjugate
  invFun := Matrix.adjugate
  left_inv M := by simp [Matrix.adjugate_adjugate M (by decide)]
  right_inv M := by simp [Matrix.adjugate_adjugate M (by decide)]
  map_add' M N := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, add_comm]
  map_smul' c M := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]

/-- The same factor swap on the binary restriction of scalars. -/
def binarySwap : V ≃ₗ[ZMod 2] V := swap.restrictScalars (ZMod 2)

@[simp] theorem binarySwap_apply (M : V) : binarySwap M = M.adjugate := rfl
@[simp] theorem binarySwap_inv : binarySwap⁻¹ = binarySwap := rfl

theorem binarySwap_conjugate (g : G) :
    binarySwap * linearAction g * binarySwap⁻¹ = linearAction (g.2, g.1) := by
  apply LinearEquiv.ext
  intro M
  change (g.1.val * M.adjugate * g.2⁻¹.val).adjugate = g.2.val * M * g.1⁻¹.val
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    ← Matrix.SpecialLinearGroup.coe_inv g.2⁻¹, inv_inv,
    Matrix.adjugate_adjugate M (by decide), ← Matrix.SpecialLinearGroup.coe_inv g.1]
  simp [mul_assoc]

private theorem linearAction_left (A : Matrix.SpecialLinearGroup (Fin 2) F) (M : V) :
    linearAction (A, 1) M = A.val * M := by
  change A.val * M * (1 : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹.val = _
  rw [inv_one, Matrix.SpecialLinearGroup.coe_one, mul_one]

/-- The conjugate associated to a determinant-one moved vector. -/
theorem conjugate_swap_apply (A : Matrix.SpecialLinearGroup (Fin 2) F) (M : V) :
    (linearAction (A, 1) * binarySwap * (linearAction (A, 1))⁻¹) M =
      A.val * M.adjugate * A.val := by
  rw [← map_inv]
  change linearAction (A, 1) (binarySwap (linearAction (A⁻¹, (1 :
    Matrix.SpecialLinearGroup (Fin 2) F)⁻¹) M)) = _
  rw [inv_one, linearAction_left, binarySwap_apply, linearAction_left,
    Matrix.adjugate_mul_distrib, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv, mul_assoc]

/-- An explicit element of order five in the first special linear factor. -/
def five : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, QuadraticAlgebra.omega], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem five_pow : five ^ 5 = 1 := by decide +kernel

theorem five_ne_one : five ≠ 1 := by decide +kernel

/-- The two swapped copies of this element give a product of involutions of order five. -/
theorem swap_product_order_eq (a : Matrix.SpecialLinearGroup (Fin 2) F) :
    orderOf (binarySwap * ((linearAction (a, 1))⁻¹ * binarySwap *
      linearAction (a, 1))) = orderOf a := by
  have hi : Function.Injective linearAction := by
    intro g h hh
    exact action_injective (congrArg LinearEquiv.toLinearMap hh)
  have he : binarySwap * ((linearAction (a, 1))⁻¹ * binarySwap *
      linearAction (a, 1)) = linearAction (a, a⁻¹) := by
    calc
      _ = (binarySwap * linearAction ((a, 1)⁻¹) * binarySwap⁻¹) *
          linearAction (a, 1) := by rw [map_inv, binarySwap_inv]; simp only [mul_assoc]
      _ = linearAction (1, a⁻¹) * linearAction (a, 1) := by
        rw [binarySwap_conjugate]
        simp only [Prod.fst_inv, Prod.snd_inv, inv_one]
      _ = _ := by
        rw [← map_mul]
        congr 1
        exact Prod.ext (one_mul _) (mul_one _)
  rw [he, orderOf_injective _ hi]
  simp only [Prod.orderOf, orderOf_inv, Nat.lcm_self]

/-- The explicit conjugate product for the swap has order five. -/
theorem swap_product_order :
    orderOf (binarySwap * ((linearAction (five, 1))⁻¹ * binarySwap *
      linearAction (five, 1))) = 5 := by
  rw [swap_product_order_eq]
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime five_pow five_ne_one

/-- The obstruction survives conjugation by any element of the two-factor group. -/
theorem conjugate_swap_product (a : G) :
    ∃ g : G, orderOf
      ((linearAction a * binarySwap * (linearAction a)⁻¹) *
       ((linearAction g)⁻¹ * (linearAction a * binarySwap * (linearAction a)⁻¹) *
        linearAction g)) = 5 := by
  refine ⟨a * (five, 1) * a⁻¹, ?_⟩
  let e := MulAut.conj (linearAction a)
  have he : linearAction (a * (five, 1) * a⁻¹) = e (linearAction (five, 1)) := by
    simp [e]
  rw [he]
  change orderOf (e binarySwap * ((e (linearAction (five, 1)))⁻¹ * e binarySwap *
    e (linearAction (five, 1)))) = 5
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact (orderOf_injective e.toMonoidHom e.injective _).trans swap_product_order

end Representation.RankTwo.OrthogonalFour
