module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Marks
public import Theory.SpecificGroups.PSL3.SmallCompletion.CubicPointCentralizer

/-!
# The original cubic line is determined by the exterior cycle

Within the literal point parabolic, every cubic commuting with the chosen
exterior cycle generates the same full torus as the retained torus word.
Only the orientation of its generator can differ.
-/

public noncomputable section
open Subgroup Matrix
namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion

private theorem torus_mem_full_torus : torus∈Matrix.PSL3.CartanActions.torus F := by
  change fieldMap nativeTorus∈(Matrix.PSL3.CartanActions.torus F).comap (Matrix.PSL3.projection F)
  rw [torus_comap,mem_torusSL_iff]
  intro i j hij
  change Representation.SL2FourNatural.fieldEquiv (nativeTorus.val i j)=0
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | simp [nativeTorus]

/-- A cubic in the point parabolic centralizing the retained exterior cycle
generates precisely the line of the canonical shared torus word. -/
theorem point_cycle_cubic_line (x : PSL) (hx : x∈pointParabolic F)
    (hx3 : orderOf x=3) (hxc : Commute x cycle) : zpowers x=zpowers torus := by
  have hTcard : Nat.card (Matrix.PSL3.CartanActions.torus F)=3 := by
    have hc := BorelQuotient.card_torus_mul_scalar F
    rw [card_F] at hc
    norm_num at hc
    omega
  have hxT : x∈Matrix.PSL3.CartanActions.torus F := by
    apply point_cycle_centralizer_le_torus F x hx
    rwa [←cycle_eq_reflections]
  have hxline : zpowers x=Matrix.PSL3.CartanActions.torus F := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hxT)
    rw [Nat.card_zpowers,hx3,hTcard]
  have htline : zpowers torus=Matrix.PSL3.CartanActions.torus F := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr torus_mem_full_torus)
    rw [Nat.card_zpowers,canonical_orders.1,hTcard]
  exact hxline.trans htline.symm

end Matrix.PSL3Four.MathieuAmalgamMarking
