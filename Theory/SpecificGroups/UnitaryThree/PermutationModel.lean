module

public import Theory.FieldTheory.Nine
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Hermitian permutation model in dimension three over F₉

The affine isotropic points of the anti-diagonal Hermitian form are pairs
`(x,y)` with `y + star y + star x * x = 0`. Their multiplication is the
upper triangular root-group law. Adjoining the point at infinity gives
28 points. Root translations, the multiplicative group of F₉, and reciprocal
coordinates generate a concrete permutation group.

This module defines that group without assuming its identification with a
matrix group. The latter must account for the anti-diagonal Gram matrix
and for coefficient transport to the standard Galois-field model.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections IV–VI. Our second coordinate is the negative of Suzuki's β.
-/

open FiniteField

namespace UnitaryThree

-- Reduction of these finite coordinates is part of the computational API.
@[expose] public section
abbrev Root := {p : Nine × Nine // p.2 + star p.2 + star p.1 * p.1 = 0}
instance : Fintype Root := inferInstance
instance : DecidableEq Root := inferInstance
instance : One Root := ⟨⟨(0, 0), by simp⟩⟩
instance : Mul Root := ⟨fun p q => ⟨(p.val.1 + q.val.1,
  p.val.2 + q.val.2 - star p.val.1 * q.val.1), by
  simp only [star_sub, star_add, star_mul, star_star]
  linear_combination p.property + q.property⟩⟩
instance : Inv Root := ⟨fun p => ⟨(-p.val.1, star p.val.2), by
  simpa only [star_neg, star_star, neg_mul_neg, add_comm (star p.val.2) p.val.2]
    using p.property⟩⟩
instance : Group Root where
  mul_assoc p q r := by
    apply Subtype.ext
    apply Prod.ext
    · exact add_assoc _ _ _
    · change (p.val.2 + q.val.2 - star p.val.1 * q.val.1) + r.val.2 -
        star (p.val.1 + q.val.1) * r.val.1 =
        p.val.2 + (q.val.2 + r.val.2 - star q.val.1 * r.val.1) -
        star p.val.1 * (q.val.1 + r.val.1)
      rw [star_add]
      ring
  one_mul p := by apply Subtype.ext; change (0 + _, 0 + _ - star (0 : Nine) * _) = _; simp
  mul_one p := by apply Subtype.ext; change (_ + 0, _ + 0 - _ * 0) = _; simp
  inv_mul_cancel p := by
    apply Subtype.ext
    apply Prod.ext
    · exact neg_add_cancel _
    · change star p.val.2 + p.val.2 - star (-p.val.1) * p.val.1 = 0
      simpa [star_neg, add_comm, sub_neg_eq_add] using p.property
theorem root_card : Fintype.card Root = 27 := by decide
theorem root_cube (p : Root) : p ^ 3 = 1 := by
  have h : ∀ p : Root, p ^ 3 = 1 := by decide +kernel
  exact h p

def scale (r : Nineˣ) (p : Root) : Root :=
  ⟨((r : Nine) * p.val.1, star (r : Nine) * r * p.val.2), by
    simp only [star_mul, star_star]
    linear_combination (star (r : Nine) * r) * p.property⟩

@[simp] theorem scale_one (p : Root) : scale 1 p = p := by
  apply Subtype.ext
  simp [scale]

@[simp] theorem scale_mul (r s : Nineˣ) (p : Root) :
    scale (r * s) p = scale r (scale s p) := by
  apply Subtype.ext
  apply Prod.ext <;> simp only [scale, Units.val_mul, star_mul] <;> ring

def scaleAut (r : Nineˣ) : Root ≃* Root where
  toFun := scale r
  invFun := scale r⁻¹
  left_inv p := by rw [← scale_mul, inv_mul_cancel, scale_one]
  right_inv p := by rw [← scale_mul, mul_inv_cancel, scale_one]
  map_mul' p q := by
    apply Subtype.ext
    apply Prod.ext
    · change (r : Nine) * (p.val.1 + q.val.1) = _ * _ + _ * _
      ring
    · change star (r : Nine) * r * (p.val.2 + q.val.2 - star p.val.1 * q.val.1) =
        star (r : Nine) * r * p.val.2 + star (r : Nine) * r * q.val.2 -
        star ((r : Nine) * p.val.1) * ((r : Nine) * q.val.1)
      rw [star_mul]
      ring

abbrev Point := Option Root

def rootPerm (p : Root) : Equiv.Perm Point := Equiv.optionCongr (Equiv.mulLeft p)
def torusPerm (r : Nineˣ) : Equiv.Perm Point := Equiv.optionCongr (scaleAut r).toEquiv

def reciprocal (p : Root) : Root :=
  ⟨(p.val.1 / p.val.2, p.val.2⁻¹), by
    have hc : ∀ x y : Nine, y + star y + star x * x = 0 →
        y⁻¹ + star (y⁻¹) + star (x / y) * (x / y) = 0 := by decide +kernel
    exact hc _ _ p.property⟩

def swapFun : Point → Point
  | none => some 1
  | some p => if p = 1 then none else some (reciprocal p)

set_option maxRecDepth 10000 in
theorem swapFun_involutive : Function.Involutive swapFun := by
  change ∀ x, swapFun (swapFun x) = x
  decide +kernel

def swapPerm : Equiv.Perm Point :=
  ⟨swapFun, swapFun, swapFun_involutive, swapFun_involutive⟩

def Model : Subgroup (Equiv.Perm Point) :=
  Subgroup.closure (Set.range rootPerm ∪ Set.range torusPerm ∪ {swapPerm})

theorem point_card : Fintype.card Point = 28 := by decide

end
end UnitaryThree
