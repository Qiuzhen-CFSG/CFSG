module
public import Theory.Representation.BinaryPermutation.FiveCentralizerSpan

/-!
# The complementary nonsingular orbit in the binary five-point module

The cubic fixing v=e₁₂ permutes the three nonzero vectors in the plane
supported on the remaining three coordinates. These are precisely the
conjugates of z+v. Each is a cubic displacement, the plane has order four,
and v is outside it. The full stabilizer of v preserves this plane.

The calculations use the actual binary augmentation core. They supply the
local moved plane in Aschbacher--Smith 13.2.12, printed p.882, with its
ambient transport in Chapter13/Section06/CentralizerReduction/LocalSetup.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.FiveCentralizerGeometry.ComplementSpan
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _

def plane : Subgroup (Multiplicative Space) where
  carrier := {x | x.toAdd.val 0 = 0 ∧ x.toAdd.val 1 = 0}
  one_mem' := ⟨rfl,rfl⟩
  mul_mem' {x y} hx hy := by
    constructor
    · change x.toAdd.val 0 + y.toAdd.val 0 = 0
      rw [hx.1,hy.1,add_zero]
    · change x.toAdd.val 1 + y.toAdd.val 1 = 0
      rw [hx.2,hy.2,add_zero]
  inv_mem' {x} hx := by
    constructor <;> change -_ = 0
    · rw [hx.1,neg_zero]
    · rw [hx.2,neg_zero]

local instance : DecidablePred (· ∈ plane) := fun x =>
  inferInstanceAs (Decidable (x.toAdd.val 0 = 0 ∧ x.toAdd.val 1 = 0))
local instance : Fintype plane := Subtype.fintype _

theorem plane_card : Nat.card plane = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def point (i : Fin 3) : Space := ![z + v, act cubic (z + v), act (cubic ^ 2) (z + v)] i

theorem points_mem (i : Fin 3) : Multiplicative.ofAdd (point i) ∈ plane := by
  fin_cases i <;> decide +kernel

theorem plane_cases (x : Space) (hx : Multiplicative.ofAdd x ∈ plane) :
    x = 0 ∨ ∃ i : Fin 3, x = point i := by
  have h : ∀ x : Space, x.val 0 = 0 ∧ x.val 1 = 0 →
      x = 0 ∨ ∃ i : Fin 3, x = point i := by decide +kernel
  exact h x hx

theorem plane_invariant (g : alternatingGroup (Fin 5)) (hg : act g v = v)
    (x : Multiplicative Space) (hx : x ∈ plane) :
    Multiplicative.ofAdd (act g x.toAdd) ∈ plane := by
  have hv : ∀ i : Fin 5, v.val i = 1 → i = 0 ∨ i = 1 := by decide +kernel
  have h0 := hv (g.val.symm 0) (congrArg (fun y : Space => y.val 0) hg)
  have h1 := hv (g.val.symm 1) (congrArg (fun y : Space => y.val 1) hg)
  change x.toAdd.val (g.val.symm 0) = 0 ∧ x.toAdd.val (g.val.symm 1) = 0
  exact ⟨h0.elim (fun h => by rw [h]; exact hx.1) (fun h => by rw [h]; exact hx.2),
    h1.elim (fun h => by rw [h]; exact hx.1) (fun h => by rw [h]; exact hx.2)⟩

theorem v_not_mem_plane : Multiplicative.ofAdd v ∉ plane := by decide +kernel

theorem point_mem_commutator (i : Fin 3) :
    ∃ j : Fin 3, point i = act cubic (point j) - point j := by
  fin_cases i <;> decide +kernel

end BinaryPermutation.FiveCentralizerGeometry.ComplementSpan
