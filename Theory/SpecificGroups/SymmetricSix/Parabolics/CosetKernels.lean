module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarActions
public import Theory.GroupAction.CoreFreeCosetQuotient

/-!
# Faithful polar parabolic coset actions

In a faithful transitive action a point stabilizer has trivial normal core.
Applying this to the actual binary polar point and line actions gives the
four A₆/S₆ parabolic core calculations. Pullback through an actual surjection
then identifies the original coset-action kernel with the quotient kernel.

Source: Aschbacher–Smith I.5.4(1) and I.5.8(2), printed pp.420–421.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix
open Subgroup


theorem duadStabilizer_normalCore : duadStabilizer.normalCore = ⊥ := by
  rw [← polarPoint_stabilizer_base]
  exact MulAction.stabilizer_normalCore_eq_bot_of_faithful _

theorem synthemeStabilizer_normalCore : synthemeStabilizer.normalCore = ⊥ := by
  rw [← polarLine_stabilizer_base]
  exact MulAction.stabilizer_normalCore_eq_bot_of_faithful _

theorem a6DuadStabilizer_normalCore : a6DuadStabilizer.normalCore = ⊥ := by
  rw [← a6_polarPoint_stabilizer_base]
  exact MulAction.stabilizer_normalCore_eq_bot_of_faithful _

theorem a6SynthemeStabilizer_normalCore : a6SynthemeStabilizer.normalCore = ⊥ := by
  rw [← a6_polarLine_stabilizer_base]
  exact MulAction.stabilizer_normalCore_eq_bot_of_faithful _

end Theory.SpecificGroups.SymmetricSix
