module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection
public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeRows

/-!
# Multiplicity models for the sparse opposite-pair branch of Table I

The four explicit multiplicity vectors for S, T, U, and V satisfy the orbit
Gram equations, contain the principal row, and contain an opposite-pair row.
The coefficient computations and their relation to the actual `tableIMatrix`
rows are proved in `TableISparseOppositeRows`.

This is the model verification stage. Exhaustive row support, the converse
integer multiplicity enumeration, and transport from arbitrary finite row
indices are separate proof obligations; no exhaustiveness is assumed here.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Cases 7–8.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows

/-- All four actual Table I multiplicity models solve the required finite
integer system, retaining the principal and opposite-pair conditions. -/
theorem modelCounts_constraints (v : Fin 4) :
    MultiplicityConstraints (modelCounts v) := by
  constructor
  · revert v
    decide +kernel
  · revert v
    decide
  · revert v
    decide

/-- The four model labels are exactly the outcomes in source Case 8. -/
theorem modelCase_cases (v : Fin 4) :
    modelCase v = .S ∨ modelCase v = .T ∨
      modelCase v = .U ∨ modelCase v = .V := by
  fin_cases v <;> decide

end Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows
