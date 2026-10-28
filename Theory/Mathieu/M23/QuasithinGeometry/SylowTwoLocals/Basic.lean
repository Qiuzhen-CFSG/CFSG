module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic

/-!
# Two concrete local candidates in M₂₃

The candidates are the existing stabilizer of a Witt heptad and the setwise
stabilizer of a specified three-element subset in the native degree-23 action.
This module only defines the actual subgroups. Exhaustive coverage of maximal
two-locals and the solvable-normal-subgroup calculation for the triple
stabilizer are separate mathematical obligations.

Source: GLS3, Table 5.3d, printed p.265; the local inspection in
Aschbacher--Smith, 15.3.41--42, printed p.1138.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals

/-- Setwise stabilization of an actual triple of natural points. -/
noncomputable def tripleStabilizer : Subgroup M23 :=
  MulAction.stabilizer M23 ({0, 1, 2} : Finset (Fin 23))

/-- The two concrete candidates, without an assertion of coverage. -/
noncomputable def candidate (i : Fin 2) : Subgroup M23 :=
  if i = 0 then heptadStabilizer else tripleStabilizer

@[simp] theorem candidate_zero : candidate 0 = heptadStabilizer := rfl

@[simp] theorem candidate_one : candidate 1 = tripleStabilizer := rfl

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals
