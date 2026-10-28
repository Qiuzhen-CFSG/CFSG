module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Orbits
/-!
# Exchanging the two marked Rudvalis points

One reverse-orbital relation is checked on the literal permutation model.
The existing orbital theorem and stabilizer transitivity then construct an
actual element exchanging the base point with the marked first neighbor.

Source: the self-paired orbital in Aschbacher–Smith J.5.1, pp.445–446.
-/

public section
noncomputable section
namespace Rudvalis.MarkedStabilizer
open MulAction OuterNormalizer

private theorem firstPoint_reverse_adj : adj firstPoint 0 := by decide +kernel

/-- The actual group exchanges the base point with the marked first point. -/
theorem exists_swap_first : ∃q:Model,q • (0 : Fin 4060)=firstPoint ∧ q • firstPoint=0 := by
  have hG := model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut
  obtain ⟨g,hg0,hg1⟩ := (adj_iff hG firstPoint 0).mp firstPoint_reverse_adj
  obtain ⟨h,hh0,hh1⟩ := root_reachable firstPoint
  rw [firstPoint_root] at hh1
  refine ⟨g*h⁻¹,?_,?_⟩
  · rw [mul_smul,inv_smul_eq_iff.mpr hh0.symm,hg0]
  · rw [mul_smul,inv_smul_eq_iff.mpr hh1.symm,hg1]
end Rudvalis.MarkedStabilizer
