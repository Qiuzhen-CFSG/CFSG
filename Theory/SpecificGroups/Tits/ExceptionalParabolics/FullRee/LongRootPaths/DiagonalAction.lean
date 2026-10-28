module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.AbelianNormalizer

/-!
# The marked diagonal centralizes the actual five-rotation

Both commuting order-four generators act by exponent three, so their ratio
centralizes the rotation and hence its whole cyclic group. This is the exact
source mark needed before identifying Q₀∩I. Source: J.4.7, printed p.442.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Subgroup RootRelations

/-- The actual cyclic diagonal centralizes the selected five-subgroup. -/
theorem Iz_le_centralizer_five : Iz ≤ centralizer (five : Set (ReeF4.Model 0)) := by
  apply zpowers_le.mpr
  have hc : Commute (s*q⁻¹) rotation := by
    change s*q⁻¹*rotation=rotation*(s*q⁻¹)
    have hsq := q_commutes_s.symm.inv_right.eq
    calc
      s*q⁻¹*rotation = q⁻¹*(s*rotation) := by rw [hsq,mul_assoc]
      _ = q⁻¹*(rotation^3*s) := by rw [s_rotation]
      _ = q⁻¹*(q*rotation)*q⁻¹*s := by rw [q_rotation]; group
      _ = rotation*(s*q⁻¹) := by rw [hsq]; group
  intro x hx
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
  exact (hc.zpow_right n).eq.symm

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
