module

public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry

/-!
# Coordinates for the A₅ Sylow flag

Coordinate changes act on the actual even-weight five-point core. A permutation
fixing v = e₁₂ sends a = e₁₃₄₅ to a or a+v, so a has a fixed, nonzero image
modulo the v-line. The stabilizer definition retains the literal subgroup of
any specified permutation group, for the local Sylow index calculation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the marking
paragraph on printed p.926, with Notation 13.2.1 on p.877.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
namespace FlagCoordinates
abbrev Perm := Equiv.Perm (Fin 5)
abbrev rho := coreRepresentation (Fin 5)

def coordinateEquiv (g : Perm) : Multiplicative Space ≃* Multiplicative Space where
  toFun x := Multiplicative.ofAdd (rho g x.toAdd)
  invFun x := Multiplicative.ofAdd (rho g⁻¹ x.toAdd)
  left_inv x := by
    change Multiplicative.ofAdd (rho g⁻¹ (rho g x.toAdd)) = x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv x := by
    change Multiplicative.ofAdd (rho g (rho g⁻¹ x.toAdd)) = x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' x y := congrArg Multiplicative.ofAdd (map_add (rho g) x.toAdd y.toAdd)

@[simp] theorem coordinateEquiv_apply (g : Perm) (x : Space) :
    coordinateEquiv g (Multiplicative.ofAdd x) = Multiplicative.ofAdd (rho g x) := rfl

theorem intertwine (g h : Perm) (x : Space) :
    rho h (rho g x) = rho g (rho (g⁻¹ * h * g) x) := by
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- Stabilizer in an actual subgroup of S₅ of a binary-core vector. -/
def stabilizer (H : Subgroup Perm) (x : Space) : Subgroup H where
  carrier := {h | rho h.val x = x}
  one_mem' := rfl
  mul_mem' {h k} hh hk := by
    change rho (h.val * k.val) x = x
    rw [map_mul, Module.End.mul_apply, hk, hh]
  inv_mem' {h} hh := by
    have he := congrArg (rho h.val⁻¹) hh
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

/-- Every permutation fixing v carries a to a or a+v. -/
theorem a_displacement (g : Perm) (hg : rho g v = v) :
    rho g a = a ∨ rho g a = a + v := by
  have hv : ∀ i : Fin 5, v.val i = 1 → i = 0 ∨ i = 1 := by decide
  have himage : g 1 = 0 ∨ g 1 = 1 := by
    have he := congrArg (fun x : Space => x.val (g 1)) hg
    change v.val (g.symm (g 1)) = v.val (g 1) at he
    rw [g.symm_apply_apply] at he
    exact hv (g 1) he.symm
  have ha : ∀ i : Fin 5, a.val i = if i = 1 then 0 else 1 := by decide
  have he (i : Fin 5) : (rho g a).val i = if i = g 1 then 0 else 1 := by
    change a.val (g.symm i) = _
    rw [ha]
    have hi : g.symm i = 1 ↔ i = g 1 := by
      constructor
      · intro h; exact (g.apply_symm_apply i).symm.trans (congrArg g h)
      · intro h; rw [h, g.symm_apply_apply]
    simp only [hi]
  rcases himage with h | h
  · right
    apply Subtype.ext
    ext i
    rw [he, h]
    fin_cases i <;> decide
  · left
    apply Subtype.ext
    ext i
    rw [he, h, ha]

private def zeroAtTwo : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 2 = 0}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by
    change x.toAdd.val 2 + y.toAdd.val 2 = 0
    rw [hx, hy, add_zero]
  inv_mem' {x} hx := by
    change -x.toAdd.val 2 = 0
    rw [hx, neg_zero]

theorem a_not_mem_vline : Multiplicative.ofAdd a ∉ zpowers (Multiplicative.ofAdd v) := by
  have hle : zpowers (Multiplicative.ofAdd v) ≤ zeroAtTwo := zpowers_le.mpr rfl
  intro ha
  exact (by decide : (1 : ZMod 2) ≠ 0) (hle ha)
end FlagCoordinates

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
