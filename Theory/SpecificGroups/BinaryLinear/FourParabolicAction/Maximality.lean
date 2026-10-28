module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximality of binary four-space parabolics

A proper overgroup K of a subspace stabilizer preserves the subspace of its
full transvection directions. This subspace contains the original nonzero
subspace and is proper, because all directions generate GL₄(2). The unique
nonzero proper invariant subspace of a full parabolic is its defining one.
Thus K is the original parabolic.

This supplies maximality for both marked row parabolics in Aschbacher,
*Sporadic Groups* (1994), 41.1, printed pp.219–220.
-/

public section
namespace BinaryLinear.FourParabolicAction

/-- Every nonzero proper subspace stabilizer in GL₄(2) is maximal. -/
theorem parabolic_isCoatom (W : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) : IsCoatom (BinaryLinear.parabolic W) := by
  open BinaryLinear FourCentralizerOvergroups FourParabolicAction in
  refine ⟨parabolic_ne_top hW0 hW1, ?_⟩
  intro K hK
  by_contra htop
  have hWD : W ≤ BinaryLinear.FourCentralizerOvergroups.directions K := by
    intro w hw f hf
    apply hK.le
    intro v
    change v + f v • w ∈ W ↔ v ∈ W
    exact W.add_mem_iff_left (W.smul_mem (f v) hw)
  have hD0 : BinaryLinear.FourCentralizerOvergroups.directions K ≠ ⊥ := by
    intro h
    exact hW0 (bot_unique (h ▸ hWD))
  have hD1 : BinaryLinear.FourCentralizerOvergroups.directions K ≠ ⊤ :=
    fun h => htop (BinaryLinear.FourCentralizerOvergroups.eq_top_of_directions_eq_top K h)
  have he := BinaryLinear.FourParabolicAction.parabolic_le_imp_eq hD0 hD1
    (hK.le.trans (BinaryLinear.FourCentralizerOvergroups.le_parabolic_directions K))
  exact hK.not_ge (he ▸ BinaryLinear.FourCentralizerOvergroups.le_parabolic_directions K)

end BinaryLinear.FourParabolicAction
