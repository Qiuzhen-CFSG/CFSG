module

public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic

/-!
# Coordinates for the quadratic field of order 25

We use pairs over F₅ with ω² = ω − 2. These are the field coordinates
of the existing exceptional A₇ matrix certificates in
`Theory.Alternating.theorem_5_2_3`. The explicit conjugation is fifth power.
Keeping these small computations separate avoids importing the Schur-cover
calculation into the unitary embedding.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding

structure F25 where
  re : ZMod 5
  im : ZMod 5
  deriving DecidableEq, Repr

namespace F25

def equivProd : F25 ≃ ZMod 5 × ZMod 5 where
  toFun x := (x.re, x.im)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : Fintype F25 :=
  Fintype.ofEquiv (ZMod 5 × ZMod 5) equivProd.symm

instance : Zero F25 := ⟨⟨0, 0⟩⟩
instance : One F25 := ⟨⟨1, 0⟩⟩
instance : Add F25 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg F25 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul F25 := ⟨fun x y =>
  ⟨x.re * y.re - 2 * x.im * y.im,
    x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

def fieldNorm (x : F25) : ZMod 5 :=
  x.re ^ 2 + x.re * x.im + 2 * x.im ^ 2

instance : Inv F25 := ⟨fun x =>
  ⟨(x.re + x.im) * fieldNorm x ^ 3, -x.im * fieldNorm x ^ 3⟩⟩

@[ext] theorem coordinate_ext {x y : F25}
    (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

@[simp] private theorem zero_re : (0 : F25).re = 0 := rfl
@[simp] private theorem zero_im : (0 : F25).im = 0 := rfl
@[simp] private theorem one_re : (1 : F25).re = 1 := rfl
@[simp] private theorem one_im : (1 : F25).im = 0 := rfl
@[simp] private theorem add_re (x y : F25) : (x + y).re = x.re + y.re := rfl
@[simp] private theorem add_im (x y : F25) : (x + y).im = x.im + y.im := rfl
@[simp] private theorem neg_re (x : F25) : (-x).re = -x.re := rfl
@[simp] private theorem neg_im (x : F25) : (-x).im = -x.im := rfl
@[simp] private theorem mul_re (x y : F25) :
    (x * y).re = x.re * y.re - 2 * x.im * y.im := rfl
@[simp] private theorem mul_im (x y : F25) :
    (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im := rfl

private theorem add_assoc' (a b c : F25) : a + b + c = a + (b + c) := by
  apply coordinate_ext <;> simp only [add_re, add_im, add_assoc]

private theorem zero_add' (a : F25) : 0 + a = a := by
  apply coordinate_ext <;> simp

private theorem neg_add_cancel' (a : F25) : -a + a = 0 := by
  apply coordinate_ext <;> simp

private theorem mul_assoc' (a b c : F25) : a * b * c = a * (b * c) := by
  apply coordinate_ext <;> simp only [mul_re, mul_im] <;> ring

private theorem mul_comm' (a b : F25) : a * b = b * a := by
  apply coordinate_ext <;> simp only [mul_re, mul_im] <;> ring

private theorem one_mul' (a : F25) : 1 * a = a := by
  apply coordinate_ext <;> simp

private theorem mul_inv_cancel' (a : F25) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  revert a
  all_goals decide
private theorem inv_zero' : (0 : F25)⁻¹ = 0 := by
  all_goals decide
private theorem left_distrib' (a b c : F25) :
    a * (b + c) = a * b + a * c := by
  apply coordinate_ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring

instance : Field F25 := Field.ofMinimalAxioms F25
  (by exact add_assoc') (by exact zero_add') (by exact neg_add_cancel')
  (by exact mul_assoc') (by exact mul_comm') (by exact one_mul')
  (by exact mul_inv_cancel') (by exact inv_zero') (by exact left_distrib')
  ⟨0, 1, by decide⟩

def omega : F25 := ⟨0, 1⟩


/-- The nonidentity automorphism of the quadratic field. -/
def conjugation : F25 ≃+* F25 where
  toFun x := ⟨x.re + x.im, -x.im⟩
  invFun x := ⟨x.re + x.im, -x.im⟩
  left_inv x := by apply coordinate_ext <;> simp
  right_inv x := by apply coordinate_ext <;> simp
  map_mul' x y := by apply coordinate_ext <;> simp only [mul_re, mul_im] <;> ring
  map_add' x y := by apply coordinate_ext <;> simp only [add_re, add_im] <;> ring

theorem conjugation_involutive : Function.Involutive conjugation := by
  intro x
  apply coordinate_ext <;> simp [conjugation]

theorem conjugation_eq_fifth (x : F25) : conjugation x = x ^ 5 := by
  revert x
  decide

theorem card : Nat.card F25 = 5 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

end F25
end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
