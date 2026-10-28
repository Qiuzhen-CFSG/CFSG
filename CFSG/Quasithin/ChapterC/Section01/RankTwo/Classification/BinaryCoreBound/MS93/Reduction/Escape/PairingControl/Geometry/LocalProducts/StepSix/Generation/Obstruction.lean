module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# An escaping but invariant plane in the binary natural module

The transvection (x,y,z) ↦ (x+y,y,z) acts nontrivially on the plane z=0
and nevertheless preserves it. Its cyclic subgroup therefore joins with
the plane's actual stabilizer to give that same proper parabolic.

This checks the obstruction to deducing the generation assertion on printed
p.885 of MS93 from noncentrality alone. It is a statement about the literal
SL₃(2) natural action; it is not a counterexample to all of the contrary
amalgam hypotheses. A source proof must also separate the critical line
from the selected plane, or supply another argument excluding this case.
-/

@[expose] public section

open Subgroup Matrix Matrix.PSL3Two
open scoped Matrix Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix.GenerationObstruction

/-- The elementary matrix with its nonzero off-diagonal entry at (0,1). -/
def transvection : SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

theorem transvection_mem : transvection ∈ lineParabolicSL := by
  rw [mem_lineParabolicSL_iff]
  decide

theorem transvection_square : transvection ^ 2 = 1 := by decide

/-- The selected plane is not fixed pointwise by the actor. -/
theorem plane_moved : ∃ v : Fin 3 → ZMod 2, v 2 = 0 ∧ transvection • v ≠ v := by
  exact ⟨![0, 1, 0], by decide, by decide⟩

/-- Its actual plane stabilizer and this actor still form a proper subgroup. -/
theorem stabilizer_sup_actor_ne_top : lineParabolicSL ⊔ zpowers transvection ≠ ⊤ := by
  rw [sup_eq_left.mpr (zpowers_le.mpr transvection_mem)]
  exact lineParabolicSL_ne_top
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix.GenerationObstruction
