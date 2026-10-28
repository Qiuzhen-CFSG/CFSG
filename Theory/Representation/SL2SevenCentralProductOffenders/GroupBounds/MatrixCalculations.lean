module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-!
# Three conjugates in the matrix group SL₂(7)

Let w = [0,-1;1,0], and let u and v be the upper and lower unit transvections.
The three conjugates w, uwu⁻¹, vwv⁻¹ produce u and v by explicit words.
Transvection induction then proves generation of the whole matrix group.
Every square root of −I is conjugate to w. The finite identities and conjugacy
certificate are checked by kernel reduction, without a native-decision axiom.

This supplies the concrete matrix calculation for the SL₂(7) central-product
offender reduction, motivated by Aschbacher–Smith, C.1.31–34, pp.135–137.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups
namespace Representation.BinaryOffender.SL2SevenCentralProduct.MatrixCalculations
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def w : SL(2, ZMod 7) := ⟨!![0, -1; 1, 0], by decide⟩
def u : SL(2, ZMod 7) := ⟨!![1, 1; 0, 1], by decide⟩
def v : SL(2, ZMod 7) := ⟨!![1, 0; 1, 1], by decide⟩

theorem upper_word : (w * (v * w * v⁻¹) * (u * w * u⁻¹)) ^ 16 = u := by
  decide +kernel
theorem lower_word : (w * (u * w * u⁻¹) * (v * w * v⁻¹)) ^ 16 = v := by
  decide +kernel

private theorem transvection_natCast {i j : Fin 2} (hij : i ≠ j) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij (n : ZMod 7) =
      Matrix.SpecialLinearGroup.transvection hij 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_add, Matrix.SpecialLinearGroup.transvection_add, ih, pow_succ]

theorem upper_lower_generate (K : Subgroup SL(2, ZMod 7)) (hu : u ∈ K) (hv : v ∈ K) : K = ⊤ := by
  apply top_unique
  intro x _
  refine Matrix.SL2.transvection_induction (F := ZMod 7)
    (fun x : SL(2, ZMod 7) => x ∈ K) ?_ (fun _ _ ha hb => K.mul_mem ha hb) x
  intro i j hij c
  rw [← ZMod.natCast_zmod_val c, transvection_natCast]
  apply K.pow_mem
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa only [show Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : ZMod 7) = u by decide] using hu
  · simpa only [show Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (1 : ZMod 7) = v by decide] using hv
  · exact (hij rfl).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem involution_scalar (x : SL(2, ZMod 7)) (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sqrt_neg_one_conjugate (x : SL(2, ZMod 7)) (hx : x ^ 2 = -1) :
    ∃ c : SL(2, ZMod 7), x = c * w * c⁻¹ := by
  revert x
  decide +kernel
end Representation.BinaryOffender.SL2SevenCentralProduct.MatrixCalculations
