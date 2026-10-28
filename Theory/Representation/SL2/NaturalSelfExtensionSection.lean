module
public import Theory.Representation.SL2.NaturalSelfExtensionCocycle
public import Mathlib.LinearAlgebra.Projection

/-!
# Normalized sections of binary natural SL₂ quotients

A quotient onto the natural binary SL₂ module admits a linear section that
commutes with the Weyl involution and the diagonal torus. Choose the section
on one coordinate axis and reflect it onto the other; average this section
over the odd-order torus. Inversion permutes the torus summands and preserves
the Weyl symmetry.

This is the normalization step in the self-extension splitting used for
DGS85, (9.10)(6), and its chosen complement (printed pp.149–150).
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups BigOperators
namespace Representation.SL2NaturalSelfExtension
variable {F : Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local notation "V" => Fin 2 → F
local notation "G" => SL(2,F)

noncomputable def torus : Fˣ →* G where
  toFun a := diagonal (a:F) a.ne_zero
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal,diag2_coe']
  map_mul' a b := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal,diag2_coe',mul_apply,Fin.sum_univ_two,mul_comm]

omit [CharP F 2] in
theorem torus_apply (a : Fˣ) : torus a = diagonal (a:F) a.ne_zero := by rfl

theorem swap_square : swap * swap = (1:G) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap_coe,mul_apply,Fin.sum_univ_two]

theorem swap_torus (a : Fˣ) : swap * torus a = torus a⁻¹ * swap := by
  change swap * diagonal (a:F) a.ne_zero = diagonal ((a⁻¹ : Fˣ) : F) (a⁻¹).ne_zero * swap
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap_coe,diagonal,diag2_coe',mul_apply,Fin.sum_univ_two]

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

theorem exists_normalized_section [Finite F]
    (ρ : Representation (ZMod 2) G Y) (q : Y →ₗ[ZMod 2] V)
    (hq : Function.Surjective q) (heq : ∀ g y, q (ρ g y) = natRep g (q y)) :
    ∃ j : V →ₗ[ZMod 2] Y,
      (∀ v, q (j v) = v) ∧
      (∀ v, ρ swap (j v) = j (natRep swap v)) ∧
      (∀ a : Fˣ, ∀ v, ρ (torus a) (j v) = j (natRep (torus a) v)) := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨j₀,hj₀⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj₀ (v : V) : q (j₀ v) = v := LinearMap.congr_fun hj₀ v
  let l : F →ₗ[ZMod 2] Y := j₀.comp (LinearMap.single (ZMod 2) (fun _ : Fin 2 => F) 0)
  have hl (x : F) : q (l x) = ![x,0] := by
    change q (j₀ (Pi.single 0 x)) = _
    rw [hqj₀]
    ext i
    fin_cases i <;> simp
  let j₁ : V →ₗ[ZMod 2] Y := l.comp (LinearMap.proj 0) +
    (ρ swap).comp (l.comp (LinearMap.proj 1))
  have hj₁ (v : V) : j₁ v = l (v 0)+ρ swap (l (v 1)) := rfl
  have hqj₁ (v : V) : q (j₁ v) = v := by
    rw [hj₁,map_add,heq,hl,hl,action_swap]
    ext i
    fin_cases i <;> simp
  have hρww (y : Y) : ρ swap (ρ swap y) = y := by
    rw [←Module.End.mul_apply,←map_mul,swap_square,map_one,Module.End.one_apply]
  have hwj₁ (v : V) : ρ swap (j₁ v) = j₁ (natRep swap v) := by
    rw [hj₁,hj₁,map_add,hρww,action_swap]
    exact add_comm _ _
  let j : V →ₗ[ZMod 2] Y := ∑ a : Fˣ,
    (ρ (torus a)).comp (j₁.comp (natRep (torus a⁻¹)))
  have hj (v : V) : j v = ∑ a : Fˣ, ρ (torus a) (j₁ (natRep (torus a⁻¹) v)) := by
    simp only [j,LinearMap.sum_apply,LinearMap.comp_apply]
  have hqj (v : V) : q (j v) = v := by
    rw [hj,map_sum]
    simp only [heq,hqj₁,←Module.End.mul_apply,←map_mul,←torus.map_mul,
      mul_inv_cancel,map_one,Module.End.one_apply,Finset.sum_const,Finset.card_univ]
    have heven : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    have hodd : Odd (Fintype.card Fˣ) := by
      rw [←Nat.card_eq_fintype_card,Nat.card_units]
      exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') heven odd_one
    have hc : (Fintype.card Fˣ : ZMod 2) = 1 := by
      rw [CharTwo.natCast_eq_ite,if_neg (Nat.not_even_iff_odd.mpr hodd)]
    rw [←Nat.cast_smul_eq_nsmul (ZMod 2),hc,one_smul]
  have htj (b : Fˣ) (v : V) : ρ (torus b) (j v) = j (natRep (torus b) v) := by
    rw [hj,hj,map_sum]
    apply Fintype.sum_bijective (b * ·) (Group.mulLeft_bijective b) _ _ ?_
    intro a
    simp only [_root_.mul_inv_rev,torus.map_mul,map_mul,Module.End.mul_apply]
    simp only [←Module.End.mul_apply,←map_mul,←torus.map_mul]
    simp only [inv_mul_cancel,mul_one]
  have hwj (v : V) : ρ swap (j v) = j (natRep swap v) := by
    rw [hj,hj,map_sum]
    apply (Fintype.sum_bijective (fun a : Fˣ => a⁻¹) (inv_involutive.bijective) _ _ ?_).symm
    intro a
    rw [inv_inv]
    have hρ (y : Y) : ρ swap (ρ (torus a⁻¹) y) = ρ (torus a) (ρ swap y) := by
      rw [←Module.End.mul_apply,←map_mul,swap_torus,inv_inv,map_mul,Module.End.mul_apply]
    rw [hρ,hwj₁]
    congr 2
    rw [←Module.End.mul_apply,←map_mul,←swap_torus,map_mul,Module.End.mul_apply]
  exact ⟨j,hqj,hwj,htj⟩

end Representation.SL2NaturalSelfExtension
