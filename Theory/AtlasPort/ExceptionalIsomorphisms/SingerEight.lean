module

/-
Adapted from Atlas/Comparisons/Exceptional/SingerEight.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
set_option warningAsError false

@[expose] public section


/-! # Eight cyclic Singer subgroups in SL3 over F2

These are actual subgroups of the matrix group. Their explicit generators permit
small kernel-checked matrix identities to label the natural eight-point Sylow
geometry. The final label is infinity. Conjugation by U is translation by one;
conjugation by T is negative reciprocal in the F7 projective-line marking.
No enumeration of the ambient group or externally trusted certificate is used.
-/

namespace Atlas.Comparisons.Exceptional.SingerEight
open scoped MatrixGroups
abbrev G := SL(3, ZMod 2)
def matrix (i : Fin 8) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
 ![!![0,1,1; 1,0,0; 0,1,0],
   !![0,1,1; 1,1,1; 0,1,0],
   !![0,0,1; 1,0,0; 0,1,1],
   !![0,1,0; 1,0,1; 0,1,1],
   !![0,0,1; 1,1,0; 0,1,1],
   !![0,1,0; 1,1,1; 0,1,1],
   !![0,0,1; 1,1,0; 0,1,0],
   !![0,0,1; 1,0,1; 0,1,0]] i

theorem matrix_det (i : Fin 8) : (matrix i).det = 1 := by
 fin_cases i <;> decide

def singer (i : Fin 8) : G := ⟨matrix i, matrix_det i⟩
def U : G := singer 7
def T : G := Matrix.SpecialLinearGroup.transvection (by decide : (0:Fin 3) ≠ 2) 1

theorem singer_pow_seven (i : Fin 8) : singer i ^ 7 = 1 := by
 fin_cases i <;> decide

theorem singer_ne_one (i : Fin 8) : singer i ≠ 1 := by
 fin_cases i <;> decide


local instance singerEightPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩
theorem singer_order (i : Fin 8) : orderOf (singer i) = 7 :=
 orderOf_eq_prime (singer_pow_seven i) (singer_ne_one i)

def subgroup (i : Fin 8) : Subgroup G := Subgroup.zpowers (singer i)

theorem singer_power_separates : ∀ i j : Fin 8, ∀ k : Fin 7,
 singer i = singer j ^ k.val → i = j := by decide

theorem subgroup_injective : Function.Injective subgroup := by
 intro i j h
 have hi : singer i ∈ subgroup j := h ▸ Subgroup.mem_zpowers (singer i)
 rw [subgroup, (isOfFinOrder_of_finite (singer j)).mem_zpowers_iff_mem_range_orderOf,
   singer_order] at hi
 obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hi
 exact singer_power_separates i j ⟨k, Finset.mem_range.mp hk⟩ he.symm

def shift (i : Fin 8) : Fin 8 := ![1,2,3,4,5,6,0,7] i
def invert (i : Fin 8) : Fin 8 := ![7,6,3,2,5,4,1,0] i
def exponent (i : Fin 8) : ℕ := ![3,1,2,3,4,5,5,1] i

theorem U_transition (i : Fin 8) : U * singer i = singer (shift i) ^ exponent i * U := by
 fin_cases i <;> decide

theorem T_transition (i : Fin 8) : T * singer i = singer (invert i) * T := by
 fin_cases i <;> decide


theorem subgroup_card (i : Fin 8) : Nat.card (subgroup i) = 7 := by
 rw [subgroup, Nat.card_zpowers, singer_order]

theorem subgroup_U (i : Fin 8) :
 (subgroup i).map (MulAut.conj U).toMonoidHom = subgroup (shift i) := by
 rw [subgroup, MonoidHom.map_zpowers]
 change Subgroup.zpowers (MulAut.conj U (singer i)) = _
 have he : MulAut.conj U (singer i) = singer (shift i) ^ exponent i := by
  change U * singer i * U⁻¹ = _
  rw [U_transition, mul_inv_cancel_right]
 rw [he]
 apply le_antisymm
 · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers _ _)
 · apply Subgroup.zpowers_le.mpr
   rw [mem_zpowers_pow_iff, singer_order]
   fin_cases i <;> decide

theorem subgroup_T (i : Fin 8) :
 (subgroup i).map (MulAut.conj T).toMonoidHom = subgroup (invert i) := by
 rw [subgroup, MonoidHom.map_zpowers]
 change Subgroup.zpowers (MulAut.conj T (singer i)) = _
 have he : MulAut.conj T (singer i) = singer (invert i) := by
  change T * singer i * T⁻¹ = _
  rw [T_transition, mul_inv_cancel_right]
 rw [he]
 rfl

end Atlas.Comparisons.Exceptional.SingerEight


