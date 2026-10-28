module
public import Theory.Representation.SL3.AdjointCubicCentralizer
public import Mathlib.GroupTheory.Index

/-!
# Fixed index of the ordinary adjoint cubic centralizer

The lower SL-two action on the ordinary adjoint cubic-fixed space is
its conjugation action on two-by-two matrices. The only matrices fixed
by this action are scalars: commuting with all transvections suffices.
Thus the fixed subgroup has order q and index q cubed in the space of
order q to the fourth power. Over the four-element field the index is 64.

The existing fixedRepresentationEquiv supplies the connection to the
ordinary adjoint. This calculation does not select a projective extension
from its restricted SL-three action. The determinant-twisted extension
has a different cubic-fixed module.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
B.4.14, printed p.98, and the use in 11.1.2, printed pp.763--764.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer
@[expose] public noncomputable section
variable (F : Type*) [Field F]

/-- All matrices fixed by the actual lower SL-two action. -/
def twoFixed : Subgroup (Multiplicative (Mat2 F)) where
  carrier := {D | ∀ g : SL(2,F), twoAction F g D.toAdd = D.toAdd}
  one_mem' g := map_zero _
  mul_mem' hD hE g := by
    change twoAction F g (_ + _) = _ + _
    rw [map_add,hD g,hE g]
  inv_mem' hD g := by
    change twoAction F g (-_) = -_
    rw [map_neg,hD g]

/-- Commuting with all transvections forces a scalar matrix. -/
theorem mem_twoFixed_iff (D : Multiplicative (Mat2 F)) :
    D ∈ twoFixed F ↔ ∃ c : F, Matrix.scalar (Fin 2) c = D.toAdd := by
  constructor
  · intro h
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    let g : SL(2,F) := ⟨t.toMatrix,by simp⟩
    have hh := congrArg (fun M : Mat2 F => M * g.val) (h g)
    change (g.val * D.toAdd * g⁻¹.val) * g.val = D.toAdd * g.val at hh
    have hg : g⁻¹.val * g.val = 1 := by
      rw [←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hg,Matrix.mul_one] at hh
    exact hh
  · rintro ⟨c,rfl⟩ g
    change g.val * Matrix.scalar (Fin 2) c * g⁻¹.val = Matrix.scalar (Fin 2) c
    rw [(Matrix.scalar_commute c (Commute.all c) g.val).symm.eq,Matrix.mul_assoc]
    rw [←Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one]

/-- The fixed scalar matrices have exactly one field coordinate. -/
def twoFixedEquiv : twoFixed F ≃ F where
  toFun D := D.val.toAdd 0 0
  invFun c := ⟨Multiplicative.ofAdd (Matrix.scalar (Fin 2) c),(mem_twoFixed_iff F _).mpr ⟨c,rfl⟩⟩
  left_inv D := by
    obtain ⟨c,hc⟩ := (mem_twoFixed_iff F D.val).mp D.property
    apply Subtype.ext
    change Matrix.scalar (Fin 2) (D.val.toAdd 0 0) = D.val.toAdd
    rw [←hc]
    simp
  right_inv c := by simp

/-- The ordinary adjoint cubic-fixed module has fixed index q-cubed. -/
theorem twoFixed_index [Finite F] : (twoFixed F).index = Nat.card F ^ 3 := by
  have hc : Nat.card (twoFixed F) = Nat.card F := Nat.card_congr (twoFixedEquiv F)
  have hm : Nat.card (Multiplicative (Mat2 F)) = Nat.card F ^ 4 := by
    change Nat.card (Fin 2 → Fin 2 → F) = _
    rw [Nat.card_fun,Nat.card_fun,Nat.card_fin,←pow_mul]
  have hi := (twoFixed F).index_mul_card
  rw [hc,hm] at hi
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := F))
  simpa only [pow_succ] using hi
end
end Representation.SL3.AdjointCubicCentralizer
