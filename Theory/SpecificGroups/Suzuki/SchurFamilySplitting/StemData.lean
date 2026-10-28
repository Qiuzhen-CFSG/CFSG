module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Invariants
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Scalar actions on a central stem kernel

This data records an additive-field abelianization of a group, a compatible
units action, and a central two-subgroup containing its third commutator.
The units fix the specified kernel. No kernel vanishing or splitting is
part of the data. The Suzuki root preimage constructs every field below
from the actual covering projection and split-torus conjugation.

The intended use is to kill third commutators by invariant triple maps,
then kill the fixed stem kernel by invariant pairings and the odd-order norm.
-/

public section
namespace ScalarInvariantMaps
universe u v

/-- The precise local group data for the scalar-invariant defect argument. -/
structure StemData (F : Type u) [Field F] (P : Type v) [Group P] where
  coordinate : P →* Multiplicative F
  coordinate_surjective : Function.Surjective coordinate
  coordinate_ker : coordinate.ker = commutator P
  action : Fˣ →* MulAut P
  coordinate_action : ∀ (t : Fˣ) x,
    coordinate (action t x) = Multiplicative.ofAdd (t * (coordinate x).toAdd)
  kernel : Subgroup P
  kernel_le_center : kernel ≤ Subgroup.center P
  kernel_le_commutator : kernel ≤ commutator P
  kernel_isTwoGroup : IsPGroup 2 kernel
  third_le_kernel : ⁅commutator P, (⊤ : Subgroup P)⁆ ≤ kernel
  action_kernel : ∀ (t : Fˣ) x, x ∈ kernel → action t x = x

end ScalarInvariantMaps
end
