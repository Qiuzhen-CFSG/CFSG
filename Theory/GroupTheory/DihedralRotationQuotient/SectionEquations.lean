module

public import Theory.GroupTheory.DihedralRotationQuotient
import all Theory.GroupTheory.DihedralRotationQuotient

/-!
# Evaluation equations for the distinguished dihedral lifts

This companion publishes equations for the named reflections and half-turn.
The internal import is intentional: it accesses the defining bodies only
to prove their public equations, leaving the original abstraction boundary
and module unchanged. Normalizer constructions use these equations to
identify the lifts' quotient coordinates.

Source: the split dihedral construction in Aschbacher--Smith 15.3.38,
combined manuscript (1 March 2004), printed p.1136.
-/

public section
namespace DihedralGroup.SplitSection
variable {P : Type*} [Group P] {R : Subgroup P} (d : SplitSection R)

theorem sectionMap_sr_zero : d.sectionMap (sr 0) = d.firstReflection := by rfl
theorem sectionMap_sr_one : d.sectionMap (sr 1) = d.secondReflection := by rfl
theorem sectionMap_r_two : d.sectionMap (r 2) = d.halfTurn := by rfl

theorem projection_firstReflection : d.projection d.firstReflection = sr 0 :=
  d.rightInverse _
theorem projection_secondReflection : d.projection d.secondReflection = sr 1 :=
  d.rightInverse _
theorem projection_halfTurn : d.projection d.halfTurn = r 2 :=
  d.rightInverse _

theorem halfTurn_mem_range : d.halfTurn ∈ d.sectionMap.range :=
  ⟨r 2, rfl⟩

end DihedralGroup.SplitSection
