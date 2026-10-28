module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.CubicImage

/-!
# The fixed line and moved plane for the cubic image

The cubic displacement subgroup consists exactly of even-weight vectors whose
first two coordinates vanish. Two differences of conjugates of z generate it.
The eight-element span is the join of this subgroup with the line on v; their
intersection is trivial, as their coordinate supports are disjoint.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926.
The ambient transport and its natural product map are proved in `Product`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open SpanGeometry
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _

def moved : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 0 = 0 ∧ x.toAdd.val 1 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' {x y} hx hy := by
    change x.toAdd.val 0 + y.toAdd.val 0 = 0 ∧ x.toAdd.val 1 + y.toAdd.val 1 = 0
    simp only [hx.1, hx.2, hy.1, hy.2, add_zero, and_self]
  inv_mem' {x} hx := by
    change -x.toAdd.val 0 = 0 ∧ -x.toAdd.val 1 = 0
    simp only [hx.1, hx.2, neg_zero, and_self]

local instance : DecidablePred (· ∈ moved) := fun x =>
  inferInstanceAs (Decidable (x.toAdd.val 0 = 0 ∧ x.toAdd.val 1 = 0))

def deltaOne : Space := act cubic z - z
def deltaTwo : Space := act (cubic ^ 2) z - z

theorem difference_mem (g : cubicGroup) (x : Space) :
    Multiplicative.ofAdd (act g.val x - x) ∈ moved := by
  have h0 : g.val.val.symm 0 = 0 := g.val.val.symm_apply_eq.mpr g.property.1.symm
  have h1 : g.val.val.symm 1 = 1 := g.val.val.symm_apply_eq.mpr g.property.2.symm
  change x.val (g.val.val.symm 0) - x.val 0 = 0 ∧ x.val (g.val.val.symm 1) - x.val 1 = 0
  simp only [h0, h1, sub_self, and_self]

theorem moved_cases (x : Space) (hx : Multiplicative.ofAdd x ∈ moved) :
    x = 0 ∨ x = deltaOne ∨ x = deltaTwo ∨ x = deltaOne + deltaTwo := by
  have hh : ∀ x : Space, x.val 0 = 0 → x.val 1 = 0 →
      x = 0 ∨ x = deltaOne ∨ x = deltaTwo ∨ x = deltaOne + deltaTwo := by decide +kernel
  exact hh x hx.1 hx.2

theorem moved_le_plane : moved ≤ plane := fun _ hx => hx.1.trans hx.2.symm

private def axis : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 2 = 0 ∧ x.toAdd.val 3 = 0 ∧ x.toAdd.val 4 = 0}
  one_mem' := ⟨rfl, rfl, rfl⟩
  mul_mem' {x y} hx hy := by
    change x.toAdd.val 2 + y.toAdd.val 2 = 0 ∧
      x.toAdd.val 3 + y.toAdd.val 3 = 0 ∧ x.toAdd.val 4 + y.toAdd.val 4 = 0
    simp only [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2, add_zero, and_self]
  inv_mem' {x} hx := by
    change -x.toAdd.val 2 = 0 ∧ -x.toAdd.val 3 = 0 ∧ -x.toAdd.val 4 = 0
    simp only [hx.1, hx.2.1, hx.2.2, neg_zero, and_self]

theorem line_disjoint_moved : Disjoint (zpowers (Multiplicative.ofAdd v)) moved := by
  have haxis : zpowers (Multiplicative.ofAdd v) ≤ axis := zpowers_le.mpr ⟨rfl, rfl, rfl⟩
  apply disjoint_def.mpr
  intro x hx hm
  have ha := haxis hx
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext i
  fin_cases i
  · exact hm.1
  · exact hm.2
  · exact ha.1
  · exact ha.2.1
  · exact ha.2.2

theorem plane_eq_line_sup_moved : plane = zpowers (Multiplicative.ofAdd v) ⊔ moved := by
  have hv : Multiplicative.ofAdd v ∈ zpowers (Multiplicative.ofAdd v) ⊔ moved :=
    mem_sup_left (mem_zpowers _)
  have hp (i : Fin 3) : Multiplicative.ofAdd (point i) ∈ zpowers (Multiplicative.ofAdd v) ⊔ moved := by
    have hd : Multiplicative.ofAdd (point i - v) ∈ moved := by
      fin_cases i <;> decide +kernel
    have hh := mul_mem hv (mem_sup_right hd)
    simpa only [← ofAdd_add, ← add_sub_assoc, add_sub_cancel_left] using hh
  apply le_antisymm
  · intro x hx
    change Multiplicative.ofAdd x.toAdd ∈ _
    rcases plane_cases x.toAdd hx with he | he | he | he | he | he | he | he <;> rw [he]
    · exact one_mem _
    · exact hp 0
    · exact hp 1
    · exact hp 2
    · exact mul_mem (hp 0) (hp 1)
    · exact mul_mem (hp 0) (hp 2)
    · exact mul_mem (hp 1) (hp 2)
    · exact hv
  · exact sup_le (zpowers_le.mpr rfl) moved_le_plane

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.ResidualCoordinates
