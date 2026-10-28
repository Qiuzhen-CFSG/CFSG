module
public import Theory.GroupAction.ExtraspecialCubicDisplacement
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# A moved vector in a noncentral cubic fixed group

A faithful action of an extraspecial group of order a power of three on
a finite two-group has a vector fixed by any marked noncentral cubic but
moved by the center, provided the cubic and center lie in an elementary
abelian subgroup of order nine. Otherwise fixed-point generation would
make the center act trivially, contradicting faithfulness.

Source application: Aschbacher--Smith, 11.1.2, printed pp.763--764,
retaining cubic movement on the actual selected chief section.
-/

public noncomputable section
open Subgroup
namespace IsExtraspecial
variable {P W : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [Group W] [Finite W]

/-- Faithfulness retains central movement on the marked cubic fixed group. -/
theorem exists_moved_cubic_fixed_of_faithful
    (σ : P →* MulAut W) (hσ : Function.Injective σ)
    (hW : IsPGroup 2 W) (X E : Subgroup P) [IsElementaryAbelian 3 X]
    (hX : Nat.card X = 9) (hE : Nat.card E = 3)
    (hEX : E ≤ X) (hZX : center P ≤ X) (hEZ : E ≠ center P) :
    ∃ w : W, (∀ e : E, σ e w = w) ∧ ∃ z : center P, σ z w ≠ w := by
  let _ : MulDistribMulAction P W := MulDistribMulAction.compHom _ σ
  by_contra! hn
  have hc : FixedPoints.subgroup E W ≤ FixedPoints.subgroup (center P) W := by
    intro w hw z
    exact hn w hw z
  have htop := center_fixed_eq_top_of_cubic_fixed hW X E hX hE hEX hZX hEZ hc
  have hz : center P = ⊥ := by
    apply bot_unique
    intro z hz
    have he : σ z = 1 := MulEquiv.ext (fun w => htop.ge (mem_top w) ⟨z,hz⟩)
    exact hσ (he.trans σ.map_one.symm)
  have hh := center_order_p 3 P
  rw [hz,card_bot] at hh
  norm_num at hh
end IsExtraspecial
