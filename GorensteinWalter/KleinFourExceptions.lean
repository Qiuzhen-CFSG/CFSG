module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public meta import Mathlib.Algebra.Group.Subgroup.Defs

noncomputable section

namespace GorensteinWalter

universe u

/-- In `A₄`, no nonidentity involution centralizes a non-involution. -/
public theorem no_involution_centralizes_noninvolution_alternatingGroup_four :
    ∀ a v : alternatingGroup (Fin 4),
      a ≠ 1 → a * a ≠ 1 → v * v = 1 → v * a = a * v → v = 1 := by
  classical
  native_decide

/-- In `A₅`, no nonidentity involution centralizes a non-involution. -/
public theorem no_involution_centralizes_noninvolution_alternatingGroup_five :
    ∀ a v : alternatingGroup (Fin 5),
      a ≠ 1 → a * a ≠ 1 → v * v = 1 → v * a = a * v → v = 1 := by
  classical
  native_decide

end GorensteinWalter
